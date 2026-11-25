/* SPDX-License-Identifier: MIT
 *
 * Copyright (C) 2017-2025 WireGuard LLC All Rights Reserved.
 */

package device

import (
	"bytes"
	"sort"
	"sync"
	"time"

	"golang.zx2c4.com/wireguard/conn"
)

// RoamPolicy selects how authenticated packets may update a peer's endpoint.
// The zero value is RoamOpen, which preserves the historic roaming behavior.
type RoamPolicy int

const (
	RoamOpen RoamPolicy = iota
	RoamPinned
	RoamLimited
)

// RoamRejectReason explains why an endpoint adoption was refused.
type RoamRejectReason int

const (
	RoamReasonNone RoamRejectReason = iota
	RoamReasonDisabled
	RoamReasonPinned
	RoamReasonRateLimited
	RoamReasonStaleKeypair
	RoamReasonInvalidEndpoint
)

// RoamEventKind identifies the kind of a roaming ledger entry.
type RoamEventKind int

const (
	RoamEventEndpointAdopted RoamEventKind = iota + 1
	RoamEventEndpointRejected
	RoamEventKeypairInstalled
	RoamEventKeypairPromoted
	RoamEventKeypairExpired
	RoamEventKeypairZeroed
	RoamEventHandshakeGaveUp
)

// RoamEvent is a single, bounded-size ledger record. It only retains endpoint
// strings and public key values, never conn.Endpoint or *Keypair objects.
type RoamEvent struct {
	Seq    uint64
	At     time.Time
	Kind   RoamEventKind
	Peer   NoisePublicKey
	From   string
	To     string
	Epoch  uint64
	Reason RoamRejectReason
}

// RoamPeerStatus is a point-in-time view of one peer's roaming bookkeeping.
type RoamPeerStatus struct {
	PublicKey             NoisePublicKey
	Epoch                 uint64
	Adoptions             uint64
	Rejections            uint64
	PolicyRejections      uint64
	StaleRejections       uint64
	RateRejections        uint64
	LastChange            time.Time
	LastEndpoint          string
	Installations         uint64
	Promotions            uint64
	Expirations           uint64
	HandshakeFailures     uint64
	CurrentKeypairCreated time.Time
	RekeyOverdue          bool
}

// RoamSnapshot is a point-in-time view of the device's roaming configuration,
// ledger counters and per-peer state. Reading it never mutates the ledger.
type RoamSnapshot struct {
	Policy     RoamPolicy
	Window     time.Duration
	MaxUpdates uint32
	Capacity   int
	Dropped    uint64
	LastSeq    uint64
	Peers      []RoamPeerStatus
	Events     []RoamEvent
}

const (
	defaultRoamMaxUpdates  = 8
	defaultRoamWindow      = 60 * time.Second
	defaultRoamLogCapacity = 256

	minRoamMaxUpdates  = 1
	maxRoamMaxUpdates  = 1024
	minRoamWindow      = 1 * time.Second
	maxRoamWindow      = 3600 * time.Second
	minRoamLogCapacity = 16
	maxRoamLogCapacity = 4096

	roamSnapshotDefaultLimit = 64
	roamSnapshotMaxLimit     = 1024
	roamStringLimit          = 128
)

// roamRing is a fixed capacity circular buffer of roaming events. Sequence
// numbers start at one and increase monotonically; when full, the oldest event
// is overwritten and Dropped is incremented by exactly one.
type roamRing struct {
	sync.Mutex
	ring     []RoamEvent
	head     int // index of the oldest retained event
	count    int // number of populated slots
	capacity int
	dropped  uint64
	lastSeq  uint64
}

func truncateRoamString(s string) string {
	if len(s) > roamStringLimit {
		return s[:roamStringLimit]
	}
	return s
}

// now returns the device time, using the replaceable clock when installed and
// falling back to time.Now otherwise. New code must not call time.Now directly.
func (device *Device) now() time.Time {
	if clock := device.roamClock.Load(); clock != nil {
		return (*clock)()
	}
	return time.Now()
}

// setRoamClock installs a replaceable clock, primarily for tests. A nil clock
// restores the default.
func (device *Device) setRoamClock(clock func() time.Time) {
	if clock == nil {
		device.roamClock.Store(nil)
		return
	}
	device.roamClock.Store(&clock)
}

// initRoamGuard installs the default roaming configuration. It is called by
// NewDevice; a zero-value Device lazily initializes to the same defaults on
// first use of any roaming interface.
func (device *Device) initRoamGuard() {
	device.ensureRoamConfig()
}

func (device *Device) ensureRoamConfig() {
	device.roamConfig.RLock()
	initialized := device.roamConfig.initialized
	device.roamConfig.RUnlock()
	if initialized {
		return
	}

	device.roamConfig.Lock()
	defer device.roamConfig.Unlock()
	if !device.roamConfig.initialized {
		device.roamConfig.policy = RoamOpen
		device.roamConfig.window = defaultRoamWindow
		device.roamConfig.maxUpdates = defaultRoamMaxUpdates
		device.roamConfig.initialized = true
	}

	device.roamLedger.Lock()
	if device.roamLedger.capacity == 0 {
		device.roamLedger.capacity = defaultRoamLogCapacity
		device.roamLedger.ring = make([]RoamEvent, defaultRoamLogCapacity)
	}
	device.roamLedger.Unlock()
}

// appendRoamEvent assigns the next sequence number and stores the event. It
// never panics on a zero-capacity ledger and never retains anything besides
// bounded strings and value types.
func (device *Device) appendRoamEvent(event RoamEvent) {
	ledger := &device.roamLedger
	ledger.Lock()
	defer ledger.Unlock()

	if ledger.capacity == 0 {
		ledger.capacity = defaultRoamLogCapacity
		ledger.ring = make([]RoamEvent, defaultRoamLogCapacity)
	}

	ledger.lastSeq++
	event.Seq = ledger.lastSeq
	event.At = device.now()
	event.From = truncateRoamString(event.From)
	event.To = truncateRoamString(event.To)

	if ledger.count == ledger.capacity {
		ledger.ring[ledger.head] = event
		ledger.head = (ledger.head + 1) % ledger.capacity
		ledger.dropped++
		return
	}
	ledger.ring[(ledger.head+ledger.count)%ledger.capacity] = event
	ledger.count++
}

// resizeLocked replaces the ring, preserving the most recent capacity events.
// Events that no longer fit are accounted for in dropped. Caller holds the
// ledger lock.
func (ledger *roamRing) resizeLocked(capacity int) {
	oldCapacity := ledger.capacity
	newRing := make([]RoamEvent, capacity)
	keep := ledger.count
	if keep > capacity {
		ledger.dropped += uint64(keep - capacity)
		keep = capacity
	}
	// Index of the oldest event to keep, in the old ring's coordinates.
	first := 0
	if oldCapacity > 0 {
		first = (ledger.head + ledger.count - keep) % oldCapacity
	}
	for i := 0; i < keep; i++ {
		newRing[i] = ledger.ring[(first+i)%oldCapacity]
	}
	ledger.ring = newRing
	ledger.capacity = capacity
	ledger.head = 0
	ledger.count = keep
}

func (device *Device) setRoamPolicy(policy RoamPolicy) {
	device.ensureRoamConfig()
	device.roamConfig.Lock()
	old := device.roamConfig.policy
	device.roamConfig.policy = policy
	device.roamConfig.Unlock()
	if old != policy {
		device.resetAllPeerRoamWindows()
	}
}

func (device *Device) setRoamMaxUpdates(maxUpdates uint32) {
	device.ensureRoamConfig()
	device.roamConfig.Lock()
	old := device.roamConfig.maxUpdates
	device.roamConfig.maxUpdates = maxUpdates
	device.roamConfig.Unlock()
	if old != maxUpdates {
		device.resetAllPeerRoamWindows()
	}
}

func (device *Device) setRoamWindow(window time.Duration) {
	device.ensureRoamConfig()
	device.roamConfig.Lock()
	old := device.roamConfig.window
	device.roamConfig.window = window
	device.roamConfig.Unlock()
	if old != window {
		device.resetAllPeerRoamWindows()
	}
}

func (device *Device) setRoamLogCapacity(capacity int) {
	device.ensureRoamConfig()
	device.roamLedger.Lock()
	defer device.roamLedger.Unlock()
	device.roamLedger.resizeLocked(capacity)
}

// resetAllPeerRoamWindows clears every peer's sliding window, frozen state and
// pinned latch. Epochs and the ledger are intentionally left untouched.
func (device *Device) resetAllPeerRoamWindows() {
	device.peers.RLock()
	defer device.peers.RUnlock()
	for _, peer := range device.peers.keyMap {
		peer.resetRoamWindow()
	}
}

// resetRoamWindow clears this peer's sliding window, frozen state and pinned
// latch. It is used for device-wide policy changes and explicit UAPI endpoint
// configuration.
func (peer *Peer) resetRoamWindow() {
	peer.endpoint.Lock()
	defer peer.endpoint.Unlock()
	peer.resetRoamWindowLocked()
}

// resetRoamWindowLocked performs the reset while the endpoint lock is already
// held, e.g. from the UAPI endpoint= line.
func (peer *Peer) resetRoamWindowLocked() {
	peer.endpoint.roamWindowStart = time.Time{}
	peer.endpoint.roamWindowCount = 0
	peer.endpoint.roamFrozen = false
	peer.endpoint.roamPinned = false
}

// SetEndpointFromHandshake is the entry point for authenticated handshake
// initiation and response messages. It returns true when the endpoint was
// rewritten. No keypair epoch gate applies to handshake messages.
func (peer *Peer) SetEndpointFromHandshake(endpoint conn.Endpoint) bool {
	return peer.roamDecision(endpoint, nil)
}

// SetEndpointFromPacket is the entry point for authenticated transport data
// messages. kp is the keypair that decrypted the packet. It returns true when
// the endpoint was rewritten.
func (peer *Peer) SetEndpointFromPacket(endpoint conn.Endpoint, kp *Keypair) bool {
	return peer.roamDecision(endpoint, kp)
}

func (peer *Peer) currentEndpointString() string {
	peer.endpoint.Lock()
	defer peer.endpoint.Unlock()
	if peer.endpoint.val == nil {
		return ""
	}
	return truncateRoamString(peer.endpoint.val.DstToString())
}

// keypairEpochAllowed reports whether kp is a current-generation keypair for
// transport-path roaming. A current keypair must carry the live epoch, while a
// next keypair must carry a strictly newer epoch. Previous and stale keypairs
// never qualify.
func (peer *Peer) keypairEpochAllowed(kp *Keypair) bool {
	peer.keypairs.RLock()
	defer peer.keypairs.RUnlock()
	epoch := peer.keyEpoch.Load()
	switch {
	case peer.keypairs.current == kp:
		return kp.epoch == epoch
	case peer.keypairs.next.Load() == kp:
		return kp.epoch > epoch
	default:
		// previous keypair or an unknown, already-rotated-out keypair
		return false
	}
}

// roamDecision is the shared admission function behind both roaming entry
// points. It never starts goroutines and never retains the packet buffers.
func (peer *Peer) roamDecision(endpoint conn.Endpoint, kp *Keypair) bool {
	device := peer.device
	if device == nil {
		return false
	}
	device.ensureRoamConfig()

	// A closed device or stopped peer accepts no changes and writes no events.
	// Check this before touching the ledger so that a late invalid endpoint
	// cannot sneak an event in after shutdown.
	if device.isClosed() || !peer.isRunning.Load() {
		return false
	}

	// Invalid endpoint: the interface nil check happens before any method call.
	if endpoint == nil {
		peer.roamReject("", "", peer.keyEpoch.Load(), RoamReasonInvalidEndpoint)
		return false
	}
	newEndpoint := truncateRoamString(endpoint.DstToString())
	if newEndpoint == "" {
		peer.roamReject(peer.currentEndpointString(), "", peer.keyEpoch.Load(), RoamReasonInvalidEndpoint)
		return false
	}

	// Snapshot the device policy.
	device.roamConfig.RLock()
	policy := device.roamConfig.policy
	window := device.roamConfig.window
	maxUpdates := device.roamConfig.maxUpdates
	device.roamConfig.RUnlock()

	// Equality short-circuit and the disableRoaming override are evaluated
	// under the endpoint lock.
	peer.endpoint.Lock()
	if peer.endpoint.val != nil && peer.endpoint.val.DstToString() == newEndpoint {
		peer.endpoint.Unlock()
		return false
	}
	disabled := peer.endpoint.disableRoaming
	var currentEndpoint string
	if peer.endpoint.val != nil {
		currentEndpoint = truncateRoamString(peer.endpoint.val.DstToString())
	}
	peer.endpoint.Unlock()

	if disabled {
		// disableRoaming takes precedence over the three policies.
		peer.roamReject(currentEndpoint, newEndpoint, peer.keyEpoch.Load(), RoamReasonDisabled)
		return false
	}

	// Epoch gate for the transport path. Handshake entries pass nil.
	epoch := peer.keyEpoch.Load()
	if kp != nil && !peer.keypairEpochAllowed(kp) {
		peer.roamReject(currentEndpoint, newEndpoint, epoch, RoamReasonStaleKeypair)
		return false
	}

	now := device.now()

	// Policy gate plus the actual rewrite, serialized by the endpoint lock.
	peer.endpoint.Lock()
	if peer.endpoint.val != nil && peer.endpoint.val.DstToString() == newEndpoint {
		peer.endpoint.Unlock()
		return false
	}

	switch policy {
	case RoamPinned:
		// The latch starts clear and is set on the first authenticated
		// adoption. Explicit UAPI endpoint= clears it again, so the next
		// packet may re-pin the peer.
		if peer.endpoint.roamPinned {
			peer.endpoint.Unlock()
			peer.roamReject(currentEndpoint, newEndpoint, epoch, RoamReasonPinned)
			return false
		}

	case RoamLimited:
		if peer.endpoint.roamWindowStart.IsZero() {
			peer.endpoint.roamWindowStart = now
		} else {
			elapsed := now.Sub(peer.endpoint.roamWindowStart)
			if elapsed < 0 {
				// Clock moved backwards: restart the window at the current
				// time without ever producing a negative duration. The
				// accumulated count and frozen state are retained.
				peer.endpoint.roamWindowStart = now
			} else if elapsed >= window {
				// The window expired, so roaming reopens automatically.
				peer.endpoint.roamWindowStart = now
				peer.endpoint.roamWindowCount = 0
				peer.endpoint.roamFrozen = false
			}
		}
		if peer.endpoint.roamFrozen {
			peer.endpoint.Unlock()
			peer.roamReject(currentEndpoint, newEndpoint, epoch, RoamReasonRateLimited)
			return false
		}
		peer.endpoint.roamWindowCount++
		if peer.endpoint.roamWindowCount >= maxUpdates {
			peer.endpoint.roamFrozen = true
		}
	}

	// Adopt: preserve the historic endpoint mutation exactly.
	peer.endpoint.val = endpoint
	peer.endpoint.clearSrcOnTx = false
	if policy == RoamPinned {
		peer.endpoint.roamPinned = true
	}
	peer.endpoint.Unlock()

	peer.roam.adoptions.Add(1)
	peer.roam.lastChange.Store(now.UnixNano())
	device.appendRoamEvent(RoamEvent{
		Kind:  RoamEventEndpointAdopted,
		Peer:  peer.handshake.remoteStatic,
		From:  currentEndpoint,
		To:    newEndpoint,
		Epoch: epoch,
	})
	return true
}

// roamReject accounts for a refused endpoint adoption and records the event.
// Rejections is the total; policy rejections cover pinned and rate limiting,
// with rate limiting as a subset, while stale keypairs have their own counter.
func (peer *Peer) roamReject(from, to string, epoch uint64, reason RoamRejectReason) {
	peer.roam.rejections.Add(1)
	switch reason {
	case RoamReasonPinned, RoamReasonRateLimited:
		peer.roam.policyRejections.Add(1)
		if reason == RoamReasonRateLimited {
			peer.roam.rateRejections.Add(1)
		}
	case RoamReasonStaleKeypair:
		peer.roam.staleRejections.Add(1)
	}
	peer.device.appendRoamEvent(RoamEvent{
		Kind:   RoamEventEndpointRejected,
		Peer:   peer.handshake.remoteStatic,
		From:   from,
		To:     to,
		Epoch:  epoch,
		Reason: reason,
	})
}

// recordKeypairEvent emits a keypair lifecycle event with the given epoch.
func (peer *Peer) recordKeypairEvent(kind RoamEventKind, epoch uint64) {
	peer.device.appendRoamEvent(RoamEvent{
		Kind:  kind,
		Peer:  peer.handshake.remoteStatic,
		Epoch: epoch,
	})
}

// RoamingSnapshot returns the roaming configuration, ledger counters, per-peer
// status and the events whose sequence number exceeds sinceSeq. A non-positive
// limit defaults to 64 and the limit is capped at 1024. The snapshot is not
// atomic across peers, but event sequence numbers never repeat or go back.
func (device *Device) RoamingSnapshot(sinceSeq uint64, limit int) RoamSnapshot {
	device.ensureRoamConfig()

	if limit <= 0 {
		limit = roamSnapshotDefaultLimit
	}
	if limit > roamSnapshotMaxLimit {
		limit = roamSnapshotMaxLimit
	}

	device.roamConfig.RLock()
	snapshot := RoamSnapshot{
		Policy:     device.roamConfig.policy,
		Window:     device.roamConfig.window,
		MaxUpdates: device.roamConfig.maxUpdates,
	}
	device.roamConfig.RUnlock()

	now := device.now()

	device.roamLedger.Lock()
	snapshot.Capacity = device.roamLedger.capacity
	snapshot.Dropped = device.roamLedger.dropped
	snapshot.LastSeq = device.roamLedger.lastSeq
	for i := 0; i < device.roamLedger.count && len(snapshot.Events) < limit; i++ {
		event := device.roamLedger.ring[(device.roamLedger.head+i)%device.roamLedger.capacity]
		if event.Seq > sinceSeq {
			// Copy so the caller can never mutate the ring.
			snapshot.Events = append(snapshot.Events, event)
		}
	}
	device.roamLedger.Unlock()

	device.peers.RLock()
	peers := make([]*Peer, 0, len(device.peers.keyMap))
	for _, peer := range device.peers.keyMap {
		peers = append(peers, peer)
	}
	device.peers.RUnlock()

	sort.Slice(peers, func(i, j int) bool {
		return bytes.Compare(peers[i].handshake.remoteStatic[:], peers[j].handshake.remoteStatic[:]) < 0
	})

	snapshot.Peers = make([]RoamPeerStatus, 0, len(peers))
	for _, peer := range peers {
		snapshot.Peers = append(snapshot.Peers, peer.roamStatus(now))
	}
	return snapshot
}

func (peer *Peer) roamStatus(now time.Time) RoamPeerStatus {
	status := RoamPeerStatus{
		PublicKey:         peer.handshake.remoteStatic,
		Epoch:             peer.keyEpoch.Load(),
		Adoptions:         peer.roam.adoptions.Load(),
		Rejections:        peer.roam.rejections.Load(),
		PolicyRejections:  peer.roam.policyRejections.Load(),
		StaleRejections:   peer.roam.staleRejections.Load(),
		RateRejections:    peer.roam.rateRejections.Load(),
		Installations:     peer.roam.installations.Load(),
		Promotions:        peer.roam.promotions.Load(),
		Expirations:       peer.roam.expirations.Load(),
		HandshakeFailures: peer.roam.handshakeFailures.Load(),
	}
	if nano := peer.roam.lastChange.Load(); nano != 0 {
		status.LastChange = time.Unix(0, nano)
	}

	peer.keypairs.RLock()
	current := peer.keypairs.current
	if current == nil {
		status.RekeyOverdue = true
	} else {
		status.CurrentKeypairCreated = current.created
		switch {
		case current.sendNonce.Load() >= RejectAfterMessages:
			status.RekeyOverdue = true
		default:
			age := now.Sub(current.created)
			// A created timestamp in the future yields a negative age and
			// therefore never counts as overdue.
			status.RekeyOverdue = age > RejectAfterTime
		}
	}
	peer.keypairs.RUnlock()

	peer.endpoint.Lock()
	if peer.endpoint.val != nil {
		status.LastEndpoint = peer.endpoint.val.DstToString()
	}
	peer.endpoint.Unlock()

	return status
}
