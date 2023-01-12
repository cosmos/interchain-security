package simibc

import channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"

// Ack represents a (sent) ack committed to block state
type Ack struct {
	Ack []byte
	// The packet to which this ack is a response
	Packet channeltypes.Packet
	// The number of App.Commits that have occurred since this ack was sent
	// For example, if the ack was sent at height h, and the blockchain
	// has headers ..., h, h+1, h+2 then Commits = 3
	Commits int
}

// Packet represents a (sent) packet committed to block state
type Packet struct {
	Packet channeltypes.Packet
	// The number of App.Commits that have occurred since this packet was sent
	// For example, if the ack was sent at height h, and the blockchain
	// has headers ..., h, h+1, h+2 then Commits = 3
	Commits int
}

// OrderedOutbox is a collection of packets and acks that have been sent
// by different chains, but have not yet been delivered to their target.
// The methods take care of bookkeeping, making it easier to simulate
// a real relayed IBC connection.
//
// Each sent packet or ack can be added here. When a sufficient number of
// block commits have followed each sent packet or ack, they can be consumed:
// delivered to their target.
type OrderedOutbox struct {
	OutboxPackets map[string][]Packet
	OutboxAcks    map[string][]Ack
}

// MakeOrderedOutbox creates a new empty network link.
func MakeOrderedOutbox() OrderedOutbox {
	return OrderedOutbox{
		OutboxPackets: map[string][]Packet{},
		OutboxAcks:    map[string][]Ack{},
	}
}

// AddPacket adds an outbound packet from the sender to the counterparty.
func (n OrderedOutbox) AddPacket(sender string, packet channeltypes.Packet) {
	n.OutboxPackets[sender] = append(n.OutboxPackets[sender], Packet{packet, 0})
}

// AddAck adds an outbound ack, for future delivery to the sender of the packet
// being acked.
func (n OrderedOutbox) AddAck(sender string, ack []byte, packet channeltypes.Packet) {
	n.OutboxAcks[sender] = append(n.OutboxAcks[sender], Ack{ack, packet, 0})
}

// ConsumePackets returns the first num packets with 2 or more commits. Returned
// packets are removed from the outbox and will not be returned again (consumed).
func (n OrderedOutbox) ConsumePackets(sender string, num int) []Packet {
	ret := []Packet{}
	sz := len(n.OutboxPackets[sender])
	if sz < num {
		num = sz
	}
	for _, p := range n.OutboxPackets[sender][:num] {
		if 1 < p.Commits {
			ret = append(ret, p)
		} else {
			break
		}
	}
	n.OutboxPackets[sender] = n.OutboxPackets[sender][len(ret):]
	return ret
}

// ConsumerAcks returns the first num packets with 2 or more commits. Returned
// acks are removed from the outbox and will not be returned again (consumed).
func (n OrderedOutbox) ConsumeAcks(sender string, num int) []Ack {
	ret := []Ack{}
	sz := len(n.OutboxAcks[sender])
	if sz < num {
		num = sz
	}
	for _, a := range n.OutboxAcks[sender][:num] {
		if 1 < a.Commits {
			ret = append(ret, a)
		} else {
			break
		}
	}
	n.OutboxAcks[sender] = n.OutboxAcks[sender][len(ret):]
	return ret
}

// Commit marks a block commit, increasing the commit count for all
// packets and acks in the sender's outbox.
// When a packet or ack has 2 or more commits, it is available for
// delivery to the counterparty chain.
// Note that 2 commits are necessary instead of 1:
//   - 1st commit is necessary for the packet to included in the block
//   - 2nd commit is necessary because in practice the ibc light client
//     needs to have block h + 1 to be able to verify the packet in block h.
func (n OrderedOutbox) Commit(sender string) {
	for i := range n.OutboxPackets[sender] {
		n.OutboxPackets[sender][i].Commits += 1
	}
	for i := range n.OutboxAcks[sender] {
		n.OutboxAcks[sender][i].Commits += 1
	}
}
