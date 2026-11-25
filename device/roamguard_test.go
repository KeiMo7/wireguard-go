/* SPDX-License-Identifier: MIT
 *
 * Copyright (C) 2017-2025 WireGuard LLC All Rights Reserved.
 */

package device

import (
	"bytes"
	"encoding/binary"
	"errors"
	"fmt"
	"net"
	"net/netip"
	"sort"
	"sync"
	"testing"
	"time"

	"golang.org/x/crypto/chacha20poly1305"
	"golang.zx2c4.com/wireguard/conn"
	"golang.zx2c4.com/wireguard/ipc"
	"golang.zx2c4.com/wireguard/tun/tuntest"
)

// fakeClock is a manually advanced clock used to drive windows and key age
// deterministically.
type fakeClock struct {
	mu  sync.Mutex
	now time.Time
}

func newFakeClock() *fakeClock {
	return &fakeClock{now: time.Date(2026, 1, 1, 0, 0, 0, 0, time.UTC)}
}

func (c *fakeClock) get() time.Time {
	c.mu.Lock()
	defer c.mu.Unlock()
	return c.now
}

func (c *fakeClock) add(d time.Duration) time.Time {
	c.mu.Lock()
	defer c.mu.Unlock()
	c.now = c.now.Add(d)
	return c.now
}

// roamFakeEndpoint is a controllable conn.Endpoint for unit tests.
type roamFakeEndpoint struct {
	dst string
}

func (e *roamFakeEndpoint) ClearSrc()           {}
func (e *roamFakeEndpoint) SrcToString() string { return "" }
func (e *roamFakeEndpoint) DstToString() string { return e.dst }
func (e *roamFakeEndpoint) DstToBytes() []byte  { return []byte(e.dst) }
func (e *roamFakeEndpoint) DstIP() netip.Addr {
	addrPort, err := netip.ParseAddrPort(e.dst)
	if err != nil {
		return netip.Addr{}
	}
	return addrPort.Addr()
}
func (e *roamFakeEndpoint) SrcIP() netip.Addr { return netip.Addr{} }

// roamFakeBind is a conn.Bind that never opens sockets but can parse the fake
// endpoints used by the in-process tests.
type roamFakeBind struct{}

func (b *roamFakeBind) Open(port uint16) (fns []conn.ReceiveFunc, actualPort uint16, err error) {
	return nil, 0, nil
}
func (b *roamFakeBind) Close() error                               { return nil }
func (b *roamFakeBind) SetMark(mark uint32) error                  { return nil }
func (b *roamFakeBind) Send(bufs [][]byte, ep conn.Endpoint) error { return nil }
func (b *roamFakeBind) BatchSize() int                             { return 1 }
func (b *roamFakeBind) ParseEndpoint(s string) (conn.Endpoint, error) {
	if _, err := netip.ParseAddrPort(s); err != nil {
		return nil, err
	}
	return &roamFakeEndpoint{dst: s}, nil
}

func newRoamTestDevice(t *testing.T) (*Device, *fakeClock) {
	t.Helper()
	clock := newFakeClock()
	dev := NewDevice(
		tuntest.NewChannelTUN().TUN(),
		&roamFakeBind{},
		NewLogger(LogLevelError, "roamtest: "),
	)
	dev.setRoamClock(clock.get)
	if err := dev.Up(); err != nil {
		t.Fatalf("Up: %v", err)
	}
	t.Cleanup(func() { dev.Close() })
	return dev, clock
}

func newRoamTestPeer(t *testing.T, dev *Device) (NoisePublicKey, *Peer) {
	t.Helper()
	sk, err := newPrivateKey()
	if err != nil {
		t.Fatalf("newPrivateKey: %v", err)
	}
	pk := sk.publicKey()
	peer, err := dev.NewPeer(pk)
	if err != nil {
		t.Fatalf("NewPeer: %v", err)
	}
	return pk, peer
}

// testKeypair builds an isolated Keypair with matching send/receive AEADs so
// that the real packet processing pipeline can decrypt packets crafted in the
// test.
func testKeypair(t *testing.T, created time.Time, epoch uint64) *Keypair {
	t.Helper()
	var key [chacha20poly1305.KeySize]byte
	key[0] = 0x42
	aead, err := chacha20poly1305.New(key[:])
	if err != nil {
		t.Fatalf("chacha20poly1305.New: %v", err)
	}
	kp := &Keypair{
		send:        aead,
		receive:     aead,
		isInitiator: true,
		created:     created,
		epoch:       epoch,
	}
	kp.replayFilter.Reset()
	return kp
}

func waitFor(t *testing.T, timeout time.Duration, cond func() bool, msg string) {
	t.Helper()
	deadline := time.Now().Add(timeout)
	for time.Now().Before(deadline) {
		if cond() {
			return
		}
		time.Sleep(time.Millisecond * 5)
	}
	if !cond() {
		t.Fatalf("timed out waiting for: %s", msg)
	}
}

func countEvents(events []RoamEvent, kind RoamEventKind) int {
	n := 0
	for _, event := range events {
		if event.Kind == kind {
			n++
		}
	}
	return n
}

// allowHandshakeRetry ages the peer's last-sent-handshake timestamp so that an
// immediate re-initiation is not suppressed by the RekeyTimeout rate limit.
func allowHandshakeRetry(peer *Peer) {
	peer.handshake.mutex.Lock()
	peer.handshake.lastSentHandshake = peer.device.now().Add(-(RekeyTimeout + time.Second))
	peer.handshake.mutex.Unlock()
}

// TestRoamEpochGate verifies that the epoch gate distinguishes current,
// previous and next keypairs while handshake messages always pass it.
func TestRoamEpochGate(t *testing.T) {
	dev, _ := newRoamTestDevice(t)
	_, peer := newRoamTestPeer(t, dev)
	peer.Start()

	created := dev.now()
	current := testKeypair(t, created, 1)
	previous := testKeypair(t, created.Add(-time.Second), 0)
	next := testKeypair(t, created, 2)

	peer.keypairs.Lock()
	peer.keypairs.current = current
	peer.keypairs.previous = previous
	peer.keypairs.next.Store(next)
	peer.keypairs.Unlock()
	peer.keyEpoch.Store(1)

	ep1 := &roamFakeEndpoint{dst: "192.0.2.1:1000"}
	ep2 := &roamFakeEndpoint{dst: "192.0.2.2:2000"}
	ep3 := &roamFakeEndpoint{dst: "192.0.2.3:3000"}
	ep4 := &roamFakeEndpoint{dst: "192.0.2.4:4000"}

	// The handshake entry is not subject to the keypair epoch gate.
	if !peer.SetEndpointFromHandshake(ep1) {
		t.Fatal("handshake entry should adopt the first endpoint")
	}
	if peer.endpoint.val != ep1 {
		t.Fatal("handshake entry did not store the endpoint")
	}
	if peer.endpoint.clearSrcOnTx {
		t.Fatal("adoption must clear clearSrcOnTx")
	}

	// A current, same-epoch keypair may rewrite the endpoint.
	if !peer.SetEndpointFromPacket(ep2, current) {
		t.Fatal("current same-epoch keypair should allow roaming")
	}
	if peer.endpoint.val != ep2 {
		t.Fatal("current keypair adoption did not store the endpoint")
	}

	// A previous keypair may not rewrite the endpoint but must be counted.
	before := peer.roam.staleRejections.Load()
	if peer.SetEndpointFromPacket(ep3, previous) {
		t.Fatal("previous keypair must not rewrite the endpoint")
	}
	if peer.endpoint.val != ep2 {
		t.Fatal("rejected adoption touched the endpoint")
	}
	if got := peer.roam.staleRejections.Load(); got != before+1 {
		t.Fatalf("StaleRejections = %d, want %d", got, before+1)
	}

	// A next, strictly-newer-epoch keypair may rewrite the endpoint.
	if !peer.SetEndpointFromPacket(ep4, next) {
		t.Fatal("next newer-epoch keypair should allow roaming")
	}
	if peer.endpoint.val != ep4 {
		t.Fatal("next keypair adoption did not store the endpoint")
	}

	// An unknown keypair (already rotated out) is treated as stale.
	orphan := testKeypair(t, created, 1)
	if peer.SetEndpointFromPacket(&roamFakeEndpoint{dst: "192.0.2.9:9000"}, orphan) {
		t.Fatal("unknown keypair must not rewrite the endpoint")
	}

	// Equal endpoints are a no-op: no counters, no events.
	snapshot := dev.RoamingSnapshot(0, 1024)
	lastSeq := snapshot.LastSeq
	if peer.SetEndpointFromPacket(ep4, current) {
		t.Fatal("identical endpoint must return false")
	}
	if dev.RoamingSnapshot(0, 1024).LastSeq != lastSeq {
		t.Fatal("identical endpoint must not append an event")
	}

	// Invalid endpoints: nil interface first, then an empty stringification.
	lastSeq = dev.RoamingSnapshot(0, 1024).LastSeq
	if peer.SetEndpointFromPacket(nil, current) {
		t.Fatal("nil endpoint must be rejected")
	}
	if peer.SetEndpointFromPacket(&roamFakeEndpoint{dst: ""}, current) {
		t.Fatal("empty endpoint string must be rejected")
	}
	snapshot = dev.RoamingSnapshot(0, 1024)
	if snapshot.LastSeq != lastSeq+2 {
		t.Fatalf("LastSeq = %d, want %d", snapshot.LastSeq, lastSeq+2)
	}
	if n := countEvents(snapshot.Events, RoamEventEndpointRejected); n < 2 {
		t.Fatalf("expected at least 2 rejection events, got %d", n)
	}
	for _, event := range snapshot.Events {
		if event.Kind == RoamEventEndpointRejected && event.Reason == RoamReasonInvalidEndpoint {
			return
		}
	}
	t.Fatal("expected an invalid-endpoint rejection event")
}

// TestRoamLimitedWindow exercises the sliding window, the freeze at the
// update limit and the automatic reopen after the window expires, including a
// backwards clock jump.
func TestRoamLimitedWindow(t *testing.T) {
	dev, clock := newRoamTestDevice(t)
	if err := dev.IpcSet("roam_policy=limited\nroam_max_updates=2\nroam_window_seconds=60\n"); err != nil {
		t.Fatalf("IpcSet: %v", err)
	}
	_, peer := newRoamTestPeer(t, dev)
	peer.Start()

	first := &roamFakeEndpoint{dst: "198.51.100.1:100"}
	if !peer.SetEndpointFromHandshake(first) {
		t.Fatal("first adoption must succeed")
	}
	second := &roamFakeEndpoint{dst: "198.51.100.2:200"}
	if !peer.SetEndpointFromHandshake(second) {
		t.Fatal("second adoption must succeed and fills the window")
	}

	// The third change within the window is refused and the endpoint stays.
	third := &roamFakeEndpoint{dst: "198.51.100.3:300"}
	if peer.SetEndpointFromHandshake(third) {
		t.Fatal("third adoption within the window must be refused")
	}
	if peer.endpoint.val != second {
		t.Fatal("frozen window changed the endpoint")
	}
	status := dev.RoamingSnapshot(0, 1024).Peers[0]
	if status.RateRejections != 1 || status.PolicyRejections != 1 {
		t.Fatalf("RateRejections=%d PolicyRejections=%d, want 1/1", status.RateRejections, status.PolicyRejections)
	}

	// A backwards clock jump must not produce a negative window duration: the
	// window restarts and the next change is still governed by the fresh
	// window, not accepted because of a negative elapsed time.
	clock.add(-30 * time.Second)
	if peer.SetEndpointFromHandshake(third) {
		t.Fatal("frozen window must stay frozen immediately after a backwards jump")
	}

	// Advancing past the window reopens roaming automatically.
	clock.add(61 * time.Second)
	if !peer.SetEndpointFromHandshake(third) {
		t.Fatal("adoption after the window expired must succeed")
	}
	if peer.endpoint.val != third {
		t.Fatal("reopened window did not store the endpoint")
	}
}

// TestRoamPinnedAndUAPIReset checks the pinned latch and the explicit UAPI
// endpoint reset that bypasses the gate.
func TestRoamPinnedAndUAPIReset(t *testing.T) {
	dev, _ := newRoamTestDevice(t)
	if err := dev.IpcSet("roam_policy=pinned\n"); err != nil {
		t.Fatalf("IpcSet: %v", err)
	}
	pub, peer := newRoamTestPeer(t, dev)
	peer.Start()

	first := &roamFakeEndpoint{dst: "203.0.113.1:100"}
	if !peer.SetEndpointFromHandshake(first) {
		t.Fatal("pinned policy must accept the first endpoint")
	}
	second := &roamFakeEndpoint{dst: "203.0.113.2:200"}
	if peer.SetEndpointFromHandshake(second) {
		t.Fatal("pinned policy must refuse the second endpoint")
	}
	if peer.endpoint.val != first {
		t.Fatal("pinned endpoint changed")
	}

	// Explicit UAPI endpoint= bypasses the gate and resets the latch and
	// window state.
	cfg := fmt.Sprintf("public_key=%x\nendpoint=203.0.113.9:900\n", pub[:])
	if err := dev.IpcSet(cfg); err != nil {
		t.Fatalf("IpcSet endpoint: %v", err)
	}
	peer.endpoint.Lock()
	got := peer.endpoint.val
	pinned := peer.endpoint.roamPinned
	frozen := peer.endpoint.roamFrozen
	count := peer.endpoint.roamWindowCount
	peer.endpoint.Unlock()
	if got == nil || got.DstToString() != "203.0.113.9:900" {
		t.Fatalf("UAPI endpoint not installed: %v", got)
	}
	if pinned || frozen || count != 0 {
		t.Fatalf("UAPI endpoint did not reset window state: pinned=%v frozen=%v count=%d", pinned, frozen, count)
	}

	// With the latch cleared the next authenticated packet is adopted again.
	if !peer.SetEndpointFromHandshake(second) {
		t.Fatal("first packet after UAPI reset must be adopted under pinned policy")
	}
	if peer.endpoint.val != second {
		t.Fatal("post-reset adoption did not store the endpoint")
	}
}

// TestRoamLedgerBounded verifies ring overwrite accounting, sequence
// continuity, string truncation and concurrent snapshot safety.
func TestRoamLedgerBounded(t *testing.T) {
	dev, _ := newRoamTestDevice(t)
	if err := dev.IpcSet("roam_log_capacity=32\n"); err != nil {
		t.Fatalf("IpcSet: %v", err)
	}
	_, peer := newRoamTestPeer(t, dev)
	peer.Start()

	const writes = 40
	for i := 0; i < writes; i++ {
		ep := &roamFakeEndpoint{dst: fmt.Sprintf("192.0.2.%d:%d", i, 1000+i)}
		if !peer.SetEndpointFromHandshake(ep) {
			t.Fatalf("adoption %d failed", i)
		}
	}

	snapshot := dev.RoamingSnapshot(0, 1024)
	if len(snapshot.Events) != 32 {
		t.Fatalf("ledger length = %d, want 32", len(snapshot.Events))
	}
	if snapshot.Dropped != writes-32 {
		t.Fatalf("Dropped = %d, want %d", snapshot.Dropped, writes-32)
	}
	if snapshot.LastSeq != writes {
		t.Fatalf("LastSeq = %d, want %d", snapshot.LastSeq, writes)
	}
	for i, event := range snapshot.Events {
		if want := uint64(writes - 32 + i + 1); event.Seq != want {
			t.Fatalf("event %d Seq = %d, want %d", i, event.Seq, want)
		}
	}

	// Shrinking within the allowed range keeps the most recent events and
	// accounts for every event that no longer fits.
	const shrunk = 16
	if err := dev.IpcSet(fmt.Sprintf("roam_log_capacity=%d\n", shrunk)); err != nil {
		t.Fatalf("IpcSet shrink: %v", err)
	}
	snapshot = dev.RoamingSnapshot(0, 1024)
	if len(snapshot.Events) != shrunk {
		t.Fatalf("shrunk length = %d, want %d", len(snapshot.Events), shrunk)
	}
	if wantDropped := uint64(writes-32) + uint64(32-shrunk); snapshot.Dropped != wantDropped {
		t.Fatalf("Dropped after shrink = %d, want %d", snapshot.Dropped, wantDropped)
	}
	if snapshot.LastSeq != writes {
		t.Fatalf("LastSeq after shrink = %d, want %d", snapshot.LastSeq, writes)
	}
	for i, event := range snapshot.Events {
		if want := uint64(writes - shrunk + i + 1); event.Seq != want {
			t.Fatalf("shrunk event %d Seq = %d, want %d", i, event.Seq, want)
		}
	}

	// Endpoint strings over 128 bytes are truncated in the stored events.
	longDst := "203.0.113.1:" + repeatByte('1', 200)
	if !peer.SetEndpointFromHandshake(&roamFakeEndpoint{dst: longDst}) {
		t.Fatal("long endpoint adoption failed")
	}
	snapshot = dev.RoamingSnapshot(uint64(writes), 1024)
	if len(snapshot.Events) != 1 {
		t.Fatalf("expected one new event, got %d", len(snapshot.Events))
	}
	if len(snapshot.Events[0].To) != roamStringLimit {
		t.Fatalf("truncated length = %d, want %d", len(snapshot.Events[0].To), roamStringLimit)
	}

	// Concurrent writes and snapshots must be race clean.
	var wg sync.WaitGroup
	for i := 0; i < 8; i++ {
		wg.Add(1)
		go func(i int) {
			defer wg.Done()
			for j := 0; j < 25; j++ {
				ep := &roamFakeEndpoint{dst: fmt.Sprintf("198.51.100.%d:%d", i, j)}
				peer.SetEndpointFromHandshake(ep)
			}
		}(i)
	}
	for i := 0; i < 4; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for j := 0; j < 50; j++ {
				dev.RoamingSnapshot(0, 32)
			}
		}()
	}
	wg.Wait()

	// Reads must not mutate the ledger.
	before := dev.RoamingSnapshot(0, 1024)
	dev.RoamingSnapshot(before.LastSeq/2, 0)
	after := dev.RoamingSnapshot(0, 1024)
	if before.LastSeq != after.LastSeq || before.Dropped != after.Dropped {
		t.Fatal("RoamingSnapshot mutated the ledger")
	}

	// limit clamping: non-positive defaults to 64, values above 1024 cap.
	if got := len(dev.RoamingSnapshot(0, -1).Events); got > 64 {
		t.Fatalf("default limit returned %d events", got)
	}
}

func repeatByte(b byte, n int) string {
	buf := make([]byte, n)
	for i := range buf {
		buf[i] = b
	}
	return string(buf)
}

// TestRoamSnapshotPeerOrder verifies that peer status is returned in public
// key byte order and the limit clamps as documented.
func TestRoamSnapshotPeerOrder(t *testing.T) {
	dev, _ := newRoamTestDevice(t)

	const peerCount = 5
	keys := make([]NoisePublicKey, peerCount)
	for i := range keys {
		pk, peer := newRoamTestPeer(t, dev)
		keys[i] = pk
		_ = peer
	}

	snapshot := dev.RoamingSnapshot(0, 1024)
	if len(snapshot.Peers) != peerCount {
		t.Fatalf("peer count = %d, want %d", len(snapshot.Peers), peerCount)
	}
	sortedKeys := append([]NoisePublicKey(nil), keys...)
	sort.Slice(sortedKeys, func(i, j int) bool {
		return bytes.Compare(sortedKeys[i][:], sortedKeys[j][:]) < 0
	})
	for i, want := range sortedKeys {
		if snapshot.Peers[i].PublicKey != want {
			t.Fatalf("peer %d out of order: got %x want %x", i, snapshot.Peers[i].PublicKey, want)
		}
	}

	// Default limit of 64 applies to non-positive values.
	if got := len(dev.RoamingSnapshot(0, 0).Events); got > 64 {
		t.Fatalf("zero limit returned %d events", got)
	}
	// Values above the cap are clamped to 1024.
	if got := len(dev.RoamingSnapshot(0, 4096).Events); got > 1024 {
		t.Fatalf("uncapped limit returned %d events", got)
	}
}

// TestRekeyEvents verifies epoch advancement and lifecycle events through a
// real handshake, plus expiration/zeroing semantics under a fake clock.
func TestRekeyEvents(t *testing.T) {
	pair := genTestPair(t, false)
	pair.Send(t, Ping, nil)

	// Initiator side: the completed handshake installed one current keypair.
	initiator := pair[1].dev
	responder := pair[0].dev
	var initPeer, respPeer *Peer
	for _, p := range initiator.peers.keyMap {
		initPeer = p
	}
	for _, p := range responder.peers.keyMap {
		respPeer = p
	}

	waitFor(t, 5*time.Second, func() bool {
		return initPeer.keyEpoch.Load() == 1 && respPeer.keyEpoch.Load() == 1
	}, "both peers to reach epoch 1 after handshake")

	initSnap := initiator.RoamingSnapshot(0, 1024)
	respSnap := responder.RoamingSnapshot(0, 1024)
	if initSnap.Peers[0].Installations != 1 {
		t.Fatalf("initiator Installations = %d, want 1", initSnap.Peers[0].Installations)
	}
	if respSnap.Peers[0].Promotions != 1 {
		t.Fatalf("responder Promotions = %d, want 1", respSnap.Peers[0].Promotions)
	}
	if countEvents(initSnap.Events, RoamEventKeypairInstalled) != 1 {
		t.Fatal("initiator missing installed event")
	}
	if countEvents(respSnap.Events, RoamEventKeypairPromoted) != 1 {
		t.Fatal("responder missing promoted event")
	}

	// Trigger a rekey from the initiator. Handshake retries within
	// RekeyTimeout are no-ops and the responder rejects replayed handshake
	// timestamps, so keep trying: the retransmit timer fires after roughly
	// RekeyTimeout. Both generations advance strictly.
	deadline := time.Now().Add(2*RekeyTimeout + time.Second)
	for time.Now().Before(deadline) {
		allowHandshakeRetry(initPeer)
		initPeer.SendHandshakeInitiation(false)
		if initPeer.keyEpoch.Load() == 2 {
			break
		}
		time.Sleep(20 * time.Millisecond)
	}
	waitFor(t, 5*time.Second, func() bool {
		return initPeer.keyEpoch.Load() == 2 && respPeer.keyEpoch.Load() == 2
	}, "both peers to reach epoch 2 after rekey")

	// Expiration: nonces hit RejectAfterMessages, an event is emitted and the
	// generation advances again.
	beforeEpoch := initPeer.keyEpoch.Load()
	initPeer.ExpireCurrentKeypairs()
	if got := initPeer.keyEpoch.Load(); got != beforeEpoch+1 {
		t.Fatalf("epoch after expire = %d, want %d", got, beforeEpoch+1)
	}
	initSnap = initiator.RoamingSnapshot(0, 1024)
	if initSnap.Peers[0].Expirations != 1 {
		t.Fatalf("Expirations = %d, want 1", initSnap.Peers[0].Expirations)
	}
	if countEvents(initSnap.Events, RoamEventKeypairExpired) != 1 {
		t.Fatal("missing expired event")
	}
	if kp := initPeer.keypairs.Current(); kp == nil || kp.sendNonce.Load() != RejectAfterMessages {
		t.Fatal("expired current keypair sendNonce must equal RejectAfterMessages")
	}

	// Zeroing removes the local index from the index table and emits an event.
	var oldIndex uint32
	if kp := initPeer.keypairs.Current(); kp != nil {
		oldIndex = kp.localIndex
	}
	if oldIndex == 0 {
		t.Fatal("expected a nonzero local index before zeroing")
	}
	initPeer.ZeroAndFlushAll()
	if entry := initiator.indexTable.Lookup(oldIndex); entry.keypair != nil {
		t.Fatal("index table still resolves the zeroed keypair")
	}
	initSnap = initiator.RoamingSnapshot(0, 1024)
	if countEvents(initSnap.Events, RoamEventKeypairZeroed) != 1 {
		t.Fatal("missing zeroed event")
	}

	// RekeyOverdue thresholds under the fake clock.
	dev, clock := newRoamTestDevice(t)
	_, peer := newRoamTestPeer(t, dev)
	peer.Start()
	created := clock.get()
	kp := testKeypair(t, created, 1)
	peer.keypairs.Lock()
	peer.keypairs.current = kp
	peer.keypairs.Unlock()
	peer.keyEpoch.Store(1)

	status := dev.RoamingSnapshot(0, 1024).Peers[0]
	if status.RekeyOverdue {
		t.Fatal("fresh keypair must not be overdue")
	}
	if !status.CurrentKeypairCreated.Equal(created) {
		t.Fatalf("CurrentKeypairCreated = %v, want %v", status.CurrentKeypairCreated, created)
	}

	clock.add(RejectAfterTime + time.Second)
	status = dev.RoamingSnapshot(0, 1024).Peers[0]
	if !status.RekeyOverdue {
		t.Fatal("keypair older than RejectAfterTime must be overdue")
	}

	// A future created timestamp must never be reported overdue.
	future := testKeypair(t, clock.get().Add(time.Hour), 2)
	peer.keypairs.Lock()
	peer.keypairs.current = future
	peer.keypairs.Unlock()
	peer.keyEpoch.Store(2)
	if status = dev.RoamingSnapshot(0, 1024).Peers[0]; status.RekeyOverdue {
		t.Fatal("future-dated keypair must not be overdue")
	}

	// No current keypair means overdue.
	peer.keypairs.Lock()
	peer.keypairs.current = nil
	peer.keypairs.Unlock()
	if status = dev.RoamingSnapshot(0, 1024).Peers[0]; !status.RekeyOverdue {
		t.Fatal("missing current keypair must be overdue")
	}

	// The nonce threshold independently marks the keypair overdue.
	clock2 := newFakeClock()
	kp2 := testKeypair(t, clock2.get(), 1)
	kp2.sendNonce.Store(RejectAfterMessages)
	peer.keypairs.Lock()
	peer.keypairs.current = kp2
	peer.keypairs.Unlock()
	if status = dev.RoamingSnapshot(0, 1024).Peers[0]; !status.RekeyOverdue {
		t.Fatal("keypair at RejectAfterMessages must be overdue")
	}
}

// TestRoamUAPIValidation covers invalid UAPI values and IpcGet immutability.
func TestRoamUAPIValidation(t *testing.T) {
	dev, _ := newRoamTestDevice(t)

	before, err := dev.IpcGet()
	if err != nil {
		t.Fatalf("IpcGet: %v", err)
	}

	invalidLines := []string{
		"roam_policy=banana\n",
		"roam_max_updates=0\n",
		"roam_max_updates=1025\n",
		"roam_window_seconds=0\n",
		"roam_window_seconds=3601\n",
		"roam_log_capacity=15\n",
		"roam_log_capacity=4097\n",
		"roam_max_updates=abc\n",
	}
	for _, line := range invalidLines {
		err := dev.IpcSet(line)
		var ipcErr *IPCError
		if !errors.As(err, &ipcErr) {
			t.Fatalf("%q: expected *IPCError, got %v", line, err)
		}
		if ipcErr.ErrorCode() != ipc.IpcErrorInvalid {
			t.Fatalf("%q: code = %d, want %d", line, ipcErr.ErrorCode(), ipc.IpcErrorInvalid)
		}
	}

	// Unknown keys keep the historic error behavior.
	if err := dev.IpcSet("roam_unknown_key=1\n"); err == nil {
		t.Fatal("unknown roam key must be rejected")
	}

	after, err := dev.IpcGet()
	if err != nil {
		t.Fatalf("IpcGet: %v", err)
	}
	if before != after {
		t.Fatalf("IpcGet changed after failed sets:\nbefore:\n%s\nafter:\n%s", before, after)
	}

	// A failed line must not partially apply: set a valid limit first, then
	// attempt an out-of-range change and confirm the original survives.
	if err := dev.IpcSet("roam_policy=limited\nroam_max_updates=4\nroam_window_seconds=30\n"); err != nil {
		t.Fatalf("valid config failed: %v", err)
	}
	snap := dev.RoamingSnapshot(0, 1024)
	if snap.Policy != RoamLimited || snap.MaxUpdates != 4 || snap.Window != 30*time.Second {
		t.Fatalf("valid config not applied: %+v", snap)
	}
	if err := dev.IpcSet("roam_max_updates=9999\n"); err == nil {
		t.Fatal("out-of-range max updates must fail")
	}
	snap = dev.RoamingSnapshot(0, 1024)
	if snap.MaxUpdates != 4 {
		t.Fatalf("MaxUpdates = %d after failed set, want 4", snap.MaxUpdates)
	}
}

// switchBind is an in-memory conn.Bind with a switchable source address. Two
// instances linked through a hub exchange real WireGuard datagrams without
// touching the kernel network stack. It supports repeated Open/Close cycles,
// because Device.Up invokes BindUpdate which closes before reopening.
type switchBind struct {
	hub    *roamHub
	mu     sync.Mutex
	src    netip.AddrPort
	closed chan struct{}
	recvCh chan *roamDatagram
}

type roamDatagram struct {
	from netip.AddrPort
	data []byte
}

type roamHub struct {
	mu    sync.Mutex
	peers map[netip.AddrPort]*switchBind
}

func newRoamHub() *roamHub {
	return &roamHub{peers: make(map[netip.AddrPort]*switchBind)}
}

func (h *roamHub) register(addr netip.AddrPort, b *switchBind) {
	h.mu.Lock()
	h.peers[addr] = b
	h.mu.Unlock()
}

func (h *roamHub) unregister(addr netip.AddrPort) {
	h.mu.Lock()
	delete(h.peers, addr)
	h.mu.Unlock()
}

func (b *switchBind) setSource(addr netip.AddrPort) {
	b.mu.Lock()
	old := b.src
	b.src = addr
	b.hub.register(addr, b)
	b.mu.Unlock()
	b.hub.unregister(old)
}

type switchEndpoint netip.AddrPort

func (e switchEndpoint) ClearSrc()           {}
func (e switchEndpoint) SrcToString() string { return "" }
func (e switchEndpoint) DstToString() string { return netip.AddrPort(e).String() }
func (e switchEndpoint) DstToBytes() []byte  { return []byte(netip.AddrPort(e).String()) }
func (e switchEndpoint) DstIP() netip.Addr   { return netip.AddrPort(e).Addr() }
func (e switchEndpoint) SrcIP() netip.Addr   { return netip.Addr{} }

func (b *switchBind) Open(port uint16) ([]conn.ReceiveFunc, uint16, error) {
	b.mu.Lock()
	b.closed = make(chan struct{})
	src := b.src
	b.mu.Unlock()
	b.hub.register(src, b)

	fn := conn.ReceiveFunc(func(bufs [][]byte, sizes []int, eps []conn.Endpoint) (int, error) {
		b.mu.Lock()
		closed := b.closed
		b.mu.Unlock()
		select {
		case <-closed:
			return 0, net.ErrClosed
		case dg := <-b.recvCh:
			n := copy(bufs[0], dg.data)
			sizes[0] = n
			eps[0] = switchEndpoint(dg.from)
			return 1, nil
		}
	})
	return []conn.ReceiveFunc{fn}, src.Port(), nil
}

func (b *switchBind) Close() error {
	b.mu.Lock()
	closed := b.closed
	src := b.src
	if closed != nil {
		select {
		case <-closed:
		default:
			close(closed)
		}
	}
	b.mu.Unlock()
	b.hub.unregister(src)
	return nil
}

func (b *switchBind) SetMark(uint32) error { return nil }

func (b *switchBind) Send(bufs [][]byte, ep conn.Endpoint) error {
	dst, ok := ep.(switchEndpoint)
	if !ok {
		return errors.New("unexpected endpoint type")
	}
	b.mu.Lock()
	from := b.src
	closed := b.closed
	b.mu.Unlock()
	b.hub.mu.Lock()
	target := b.hub.peers[netip.AddrPort(dst)]
	b.hub.mu.Unlock()
	if target == nil {
		return net.ErrClosed
	}
	for _, buf := range bufs {
		payload := make([]byte, len(buf))
		copy(payload, buf)
		select {
		case <-closed:
			return net.ErrClosed
		case target.recvCh <- &roamDatagram{from: from, data: payload}:
		}
	}
	return nil
}

func (b *switchBind) ParseEndpoint(s string) (conn.Endpoint, error) {
	addrPort, err := netip.ParseAddrPort(s)
	if err != nil {
		return nil, err
	}
	return switchEndpoint(addrPort), nil
}

func (b *switchBind) BatchSize() int { return 1 }

func newSwitchDevice(t *testing.T, hub *roamHub, id string, src netip.AddrPort, ip netip.Addr) (*Device, *tuntest.ChannelTUN, *switchBind) {
	t.Helper()
	tun := tuntest.NewChannelTUN()
	bind := &switchBind{
		hub:    hub,
		src:    src,
		closed: make(chan struct{}),
		recvCh: make(chan *roamDatagram, 256),
	}
	hub.register(src, bind)
	dev := NewDevice(tun.TUN(), bind, NewLogger(LogLevelError, id+": "))
	t.Cleanup(func() { dev.Close() })
	return dev, tun, bind
}

// craftTransportPacket builds a WireGuard transport message encrypted with
// kp.send for the given plaintext IP packet.
func craftTransportPacket(t *testing.T, kp *Keypair, nonce uint64, payload []byte) []byte {
	t.Helper()
	packet := make([]byte, MessageTransportHeaderSize+len(payload)+chacha20poly1305.Overhead)
	binary.LittleEndian.PutUint32(packet[0:4], MessageTransportType)
	binary.LittleEndian.PutUint32(packet[4:8], kp.remoteIndex)
	binary.LittleEndian.PutUint64(packet[8:16], nonce)
	var nonceBytes [chacha20poly1305.NonceSize]byte
	binary.LittleEndian.PutUint64(nonceBytes[4:], nonce)
	kp.send.Seal(packet[:MessageTransportHeaderSize], nonceBytes[:], payload, nil)
	return packet
}

// TestRoamIntegrationRoaming drives two real devices through a handshake and
// ping over an in-memory bind, then verifies current-keypair roaming from a new
// source and stale-keypair delivery from a third source.
func TestRoamIntegrationRoaming(t *testing.T) {
	hub := newRoamHub()
	srcA1 := netip.MustParseAddrPort("192.0.2.1:5001")
	srcA2 := netip.MustParseAddrPort("192.0.2.2:5002")
	srcA3 := netip.MustParseAddrPort("192.0.2.3:5003")
	srcB := netip.MustParseAddrPort("198.51.100.1:6001")

	devA, tunA, bindA := newSwitchDevice(t, hub, "A", srcA1, netip.MustParseAddr("1.0.0.1"))
	devB, tunB, bindB := newSwitchDevice(t, hub, "B", srcB, netip.MustParseAddr("1.0.0.2"))

	var keyA, keyB NoisePrivateKey
	key, err := newPrivateKey()
	if err != nil {
		t.Fatal(err)
	}
	keyA = key
	key, err = newPrivateKey()
	if err != nil {
		t.Fatal(err)
	}
	keyB = key
	pubA, pubB := keyA.publicKey(), keyB.publicKey()

	cfgA := fmt.Sprintf("private_key=%x\npublic_key=%x\nendpoint=%s\nallowed_ip=1.0.0.2/32\n",
		keyA[:], pubB[:], srcB.String())
	cfgB := fmt.Sprintf("private_key=%x\npublic_key=%x\nendpoint=%s\nallowed_ip=1.0.0.1/32\n",
		keyB[:], pubA[:], srcA1.String())
	if err := devA.IpcSet(cfgA); err != nil {
		t.Fatalf("IpcSet A: %v", err)
	}
	if err := devB.IpcSet(cfgB); err != nil {
		t.Fatalf("IpcSet B: %v", err)
	}
	if err := devA.Up(); err != nil {
		t.Fatalf("Up A: %v", err)
	}
	if err := devB.Up(); err != nil {
		t.Fatalf("Up B: %v", err)
	}

	var peerA, peerB *Peer
	for _, p := range devA.peers.keyMap {
		peerA = p
	}
	for _, p := range devB.peers.keyMap {
		peerB = p
	}

	// Complete a handshake and one ping in both directions.
	ping := tuntest.Ping(netip.MustParseAddr("1.0.0.2"), netip.MustParseAddr("1.0.0.1"))
	tunA.Outbound <- ping
	select {
	case got := <-tunB.Inbound:
		if len(got) != len(ping) {
			t.Fatalf("ping length mismatch: %d != %d", len(got), len(ping))
		}
	case <-time.After(5 * time.Second):
		t.Fatal("initial ping did not reach B")
	}

	// A now sources datagrams from a second address. B adopts it on the next
	// authenticated packet.
	bindA.setSource(srcA2)
	ping2 := tuntest.Ping(netip.MustParseAddr("1.0.0.2"), netip.MustParseAddr("1.0.0.1"))
	tunA.Outbound <- ping2
	select {
	case <-tunB.Inbound:
	case <-time.After(5 * time.Second):
		t.Fatal("ping from the new source did not reach B")
	}
	waitFor(t, time.Second, func() bool {
		return peerB.currentEndpointString() == srcA2.String()
	}, "B to adopt A's new endpoint")
	status := devB.RoamingSnapshot(0, 1024).Peers[0]
	// B's endpoint was explicitly configured to srcA1, so only the move to
	// srcA2 counts as an authenticated adoption.
	if status.Adoptions != 1 {
		t.Fatalf("Adoptions = %d, want 1", status.Adoptions)
	}
	if status.LastEndpoint != srcA2.String() {
		t.Fatalf("LastEndpoint = %q, want %q", status.LastEndpoint, srcA2.String())
	}

	// Force a rekey. The handshake routine rate-limits retries within
	// RekeyTimeout and the responder rejects replayed timestamps, so keep
	// trying until the initiation is accepted. A fresh data packet then drives
	// responder promotion; once promoted, the original keypair remains as
	// previous.
	deadline := time.Now().Add(2*RekeyTimeout + time.Second)
	for time.Now().Before(deadline) && peerA.keyEpoch.Load() < 2 {
		allowHandshakeRetry(peerA)
		peerA.SendHandshakeInitiation(false)
		time.Sleep(20 * time.Millisecond)
	}
	if peerA.keyEpoch.Load() < 2 {
		t.Fatal("initiator rekey installation did not complete")
	}

	// Trigger responder promotion with a packet on the newly installed keys.
	tunA.Outbound <- tuntest.Ping(netip.MustParseAddr("1.0.0.2"), netip.MustParseAddr("1.0.0.1"))
	waitFor(t, 5*time.Second, func() bool {
		return peerB.keyEpoch.Load() >= 2
	}, "responder rekey promotion")

	// After the rekey, B still holds the first generation as previous and can
	// decrypt packets sealed with the matching A-side send key. A's previous
	// keypair carries exactly that send key. Crafting the packet manually
	// bypasses A's send pipeline, which would otherwise use the current key.
	peerB.keypairs.RLock()
	oldKeypairB := peerB.keypairs.previous
	peerB.keypairs.RUnlock()
	if oldKeypairB == nil {
		t.Fatal("B has no previous keypair after rekey")
	}
	peerA.keypairs.RLock()
	oldKeypairA := peerA.keypairs.previous
	peerA.keypairs.RUnlock()
	if oldKeypairA == nil {
		t.Fatal("A has no previous keypair after rekey")
	}

	// Quiesce the data path before switching sources. The promotion packet
	// and any retransmission travel on the current keypair and would
	// legitimately adopt a new source, so wait until B's receive queue, TUN
	// queue and ledger sequence number all stop changing.
	quiesce := func() bool {
		if len(bindB.recvCh) != 0 {
			return false
		}
		select {
		case <-tunB.Inbound:
			return false
		default:
		}
		return true
	}
	stableRounds := 0
	lastSeq := devB.RoamingSnapshot(0, 1024).LastSeq
	quiesceDeadline := time.Now().Add(5 * time.Second)
	for time.Now().Before(quiesceDeadline) {
		if quiesce() && devB.RoamingSnapshot(0, 1024).LastSeq == lastSeq {
			stableRounds++
			if stableRounds >= 10 {
				break
			}
		} else {
			stableRounds = 0
			lastSeq = devB.RoamingSnapshot(0, 1024).LastSeq
		}
		time.Sleep(5 * time.Millisecond)
	}
	if got := peerB.currentEndpointString(); got != srcA2.String() {
		t.Fatalf("endpoint before stale packet = %q, want %q", got, srcA2.String())
	}
	staleBefore := devB.RoamingSnapshot(0, 1024).Peers[0].StaleRejections

	bindA.setSource(srcA3)
	nonce := oldKeypairA.sendNonce.Load()
	packet := craftTransportPacket(t, oldKeypairA, nonce, ping)
	if err := bindA.Send([][]byte{packet}, switchEndpoint(srcB)); err != nil {
		t.Fatalf("Send stale packet: %v", err)
	}

	// B must still decrypt and deliver the packet to the TUN, while the
	// endpoint remains pinned to the adopted second address.
	select {
	case got := <-tunB.Inbound:
		if len(got) != len(ping) {
			t.Fatalf("stale packet delivered with unexpected length %d", len(got))
		}
	case <-time.After(5 * time.Second):
		t.Fatal("previous-keypair packet was not delivered")
	}
	// The stale rejection is the authoritative signal that the epoch gate
	// fired for this packet; wait for it rather than relying on timing.
	waitFor(t, time.Second, func() bool {
		return devB.RoamingSnapshot(0, 1024).Peers[0].StaleRejections > staleBefore
	}, "stale rejection to be recorded")
	if got := peerB.currentEndpointString(); got != srcA2.String() {
		t.Fatalf("stale keypair rewrote the endpoint to %q", got)
	}
	snapshot := devB.RoamingSnapshot(0, 1024)
	if snapshot.Peers[0].StaleRejections == 0 {
		t.Fatal("stale keypair adoption was not counted")
	}
}

// TestRoamClosedDevice confirms that after Close the entry points refuse
// changes without writing events, while the snapshot stays readable.
func TestRoamClosedDevice(t *testing.T) {
	clock := newFakeClock()
	dev := NewDevice(
		tuntest.NewChannelTUN().TUN(),
		&roamFakeBind{},
		NewLogger(LogLevelError, "roamtest: "),
	)
	dev.setRoamClock(clock.get)
	if err := dev.Up(); err != nil {
		t.Fatalf("Up: %v", err)
	}
	_, peer := newRoamTestPeer(t, dev)
	peer.Start()
	ep := &roamFakeEndpoint{dst: "192.0.2.1:1000"}
	if !peer.SetEndpointFromHandshake(ep) {
		t.Fatal("initial adoption failed")
	}

	// Close itself may legitimately emit lifecycle events, so the baseline
	// sequence is captured after shutdown.
	dev.Close()
	lastSeq := dev.RoamingSnapshot(0, 1024).LastSeq

	if peer.SetEndpointFromHandshake(&roamFakeEndpoint{dst: "192.0.2.2:2000"}) {
		t.Fatal("closed device must refuse endpoint changes")
	}
	if peer.endpoint.val != ep {
		t.Fatal("closed device endpoint was modified")
	}
	if got := dev.RoamingSnapshot(0, 1024).LastSeq; got != lastSeq {
		t.Fatalf("closed device appended events: LastSeq %d != %d", got, lastSeq)
	}
	// Snapshot remains readable after close.
	_ = dev.RoamingSnapshot(0, 1024)
}

// TestRoamHandshakeGiveUp verifies that exhausting the retransmit attempts
// records the give-up event and increments the failure counter without
// altering the underlying give-up logic.
func TestRoamHandshakeGiveUp(t *testing.T) {
	dev, _ := newRoamTestDevice(t)
	_, peer := newRoamTestPeer(t, dev)
	peer.Start()

	// Reproduce the state the retransmit timer enters once more than
	// MaxTimerHandshakes attempts have elapsed.
	peer.timers.handshakeAttempts.Store(MaxTimerHandshakes + 1)
	expiredRetransmitHandshake(peer)

	snapshot := dev.RoamingSnapshot(0, 1024)
	if snapshot.Peers[0].HandshakeFailures != 1 {
		t.Fatalf("HandshakeFailures = %d, want 1", snapshot.Peers[0].HandshakeFailures)
	}
	if countEvents(snapshot.Events, RoamEventHandshakeGaveUp) != 1 {
		t.Fatal("expected one handshake give-up event")
	}
	// The zero-key-material residue timer is armed by the give-up path.
	if !peer.timers.zeroKeyMaterial.IsPending() {
		t.Fatal("give-up must arm the zero key material timer")
	}
}

// TestRoamLazyDefaults ensures a zero-value Device initializes the documented
// defaults on first use of the roaming interface.
func TestRoamLazyDefaults(t *testing.T) {
	dev := &Device{}
	dev.closed = make(chan struct{})
	t.Cleanup(func() {
		// A manually allocated Device never started workers; only release the
		// ledger resources it lazily allocated.
	})
	snapshot := dev.RoamingSnapshot(0, 1024)
	if snapshot.Policy != RoamOpen ||
		snapshot.MaxUpdates != defaultRoamMaxUpdates ||
		snapshot.Window != defaultRoamWindow ||
		snapshot.Capacity != defaultRoamLogCapacity {
		t.Fatalf("lazy defaults mismatch: %+v", snapshot)
	}
}
