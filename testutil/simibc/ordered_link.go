package simibc

import channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"

type ChainID string

// Ack represents and ack committed to block state
type Ack struct {
	Ack     []byte
	Packet  channeltypes.Packet
	Commits int
}

// Packet represents a packet committed to block state
type Packet struct {
	Packet  channeltypes.Packet
	Commits int
}

// OrderedLink contains outboxes of packets and acknowledgements and
// allows fine-grained control over delivery of acks and packets
// to mimic a real relaying relationship between two chains.
type OrderedLink struct {
	OutboxPackets map[ChainID][]Packet
	OutboxAcks    map[ChainID][]Ack
}

// MakeOrderedLink creates a new empty network link.
func MakeOrderedLink() OrderedLink {
	return OrderedLink{
		OutboxPackets: map[ChainID][]Packet{},
		OutboxAcks:    map[ChainID][]Ack{},
	}
}

// AddPacket adds an outbound packet from the sender to the counterparty.
func (n OrderedLink) AddPacket(sender ChainID, packet channeltypes.Packet) {
	n.OutboxPackets[sender] = append(n.OutboxPackets[sender], Packet{packet, 0})
}

// AddAck adds an outbound ack, for future delivery to the sender of the packet
// being acked.
func (n OrderedLink) AddAck(sender ChainID, ack []byte, packet channeltypes.Packet) {
	n.OutboxAcks[sender] = append(n.OutboxAcks[sender], Ack{ack, packet, 0})
}

// ConsumePackets returns the first num packets with 2 or more commits. Returned
// packets are removed from the outbox and will not be returned again (consumed).
func (n OrderedLink) ConsumePackets(sender ChainID, num int) []Packet {
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
func (n OrderedLink) ConsumeAcks(sender ChainID, num int) []Ack {
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
func (n OrderedLink) Commit(sender ChainID) {
	for i := range n.OutboxPackets[sender] {
		n.OutboxPackets[sender][i].Commits += 1
	}
	for i := range n.OutboxAcks[sender] {
		n.OutboxAcks[sender][i].Commits += 1
	}
}
