package simibc

import channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"

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
	OutboxPackets map[string][]Packet
	OutboxAcks    map[string][]Ack
}

// MakeOrderedLink creates a new empty network link.
func MakeOrderedLink() OrderedLink {
	return OrderedLink{
		OutboxPackets: map[string][]Packet{},
		OutboxAcks:    map[string][]Ack{},
	}
}

// AddPacket adds an outbound packet from the sender to the counterparty.
func (n OrderedLink) AddPacket(sender string, packet channeltypes.Packet) {
	n.OutboxPackets[sender] = append(n.OutboxPackets[sender], Packet{packet, 0})
}

// AddAck adds an outbound ack, for future delivery to the sender of the packet
// being acked.
func (n OrderedLink) AddAck(sender string, ack []byte, packet channeltypes.Packet) {
	n.OutboxAcks[sender] = append(n.OutboxAcks[sender], Ack{ack, packet, 0})
}

// ConsumePackets returns and internally delets all packets with 2 or more commits.
func (n OrderedLink) ConsumePackets(sender string, num int) []Packet {
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

// ConsumeAcks returns and internally deletes all acks with 2 or more commits.
func (n OrderedLink) ConsumeAcks(sender string, num int) []Ack {
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

// Commit marks a block commit for a chain and will make its outbound
// packets visible as per the functioning of ibc. In practice it takes
// 2 commits for a packet to become available for delivery, due to the
// need for the light client to have block h + 1 for a packet in block
// h.
func (n OrderedLink) Commit(sender string) {
	for i := range n.OutboxPackets[sender] {
		n.OutboxPackets[sender][i].Commits += 1
	}
	for i := range n.OutboxAcks[sender] {
		n.OutboxAcks[sender][i].Commits += 1
	}
}
