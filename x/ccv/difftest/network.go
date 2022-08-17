package difftest

import channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"

type Ack struct {
	Ack     []byte
	Packet  channeltypes.Packet
	Commits int
}

type Packet struct {
	Packet  channeltypes.Packet
	Commits int
}

// Network contains outboxes of packets and acknowledgements and
// allows fine-grained control over delivery of acks and packets
// to mimic a real ibc network between two chains.
type Network struct {
	OutboxPackets map[string][]Packet
	OutboxAcks    map[string][]Ack
}

// MakeNetwork creates a new empty network.
func MakeNetwork() Network {
	return Network{
		OutboxPackets: map[string][]Packet{},
		OutboxAcks:    map[string][]Ack{},
	}
}

// AddPacket adds an outbound packet from the sender to the counterparty
func (n Network) AddPacket(sender string, packet channeltypes.Packet) {
	n.OutboxPackets[sender] = append(n.OutboxPackets[sender], Packet{packet, 0})
}

// AddAck adds an outbound ack from the sender of the ack to the counterparty.
// In this case the counterparty is the sender of the original packet being acked.
func (n Network) AddAck(sender string, ack []byte, packet channeltypes.Packet) {
	n.OutboxAcks[sender] = append(n.OutboxAcks[sender], Ack{ack, packet, 0})
}

// Consume packets returns and internally deletes all packets with 2 or more
// commits.
func (n Network) ConsumePackets(sender string, num int64) []Packet {
	ret := []Packet{}
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

// Consume acks returns and internally deletes all acks with 2 or more commits.
func (n Network) ConsumeAcks(sender string) []Ack {
	ret := []Ack{}
	for _, a := range n.OutboxAcks[sender] {
		if 1 < a.Commits {
			ret = append(ret, a)
		} else {
			break
		}
	}
	n.OutboxAcks[sender] = n.OutboxAcks[sender][len(ret):]
	return ret
}

// Commit marks a block commit for a sending chain and will make packets
// visible as the usual operation of ibc. In practice it takes 2 commits
// for a packet to become available for delivery, due to off-by one in
// the light client.
func (n Network) Commit(sender string) {

	for i := range n.OutboxPackets[sender] {
		n.OutboxPackets[sender][i].Commits += 1
	}
	for i := range n.OutboxAcks[sender] {
		n.OutboxAcks[sender][i].Commits += 1
	}
}
