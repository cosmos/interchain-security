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

type Network struct {
	OutboxPackets map[string][]Packet
	OutboxAcks    map[string][]Ack
}

func MakeNetwork() Network {
	return Network{
		OutboxPackets: map[string][]Packet{},
		OutboxAcks:    map[string][]Ack{},
	}
}

func (n Network) AddPacket(sender string, packet channeltypes.Packet) {
	n.OutboxPackets[sender] = append(n.OutboxPackets[sender], Packet{packet, 0})
}

func (n Network) AddAck(sender string, ack []byte, packet channeltypes.Packet) {
	n.OutboxAcks[sender] = append(n.OutboxAcks[sender], Ack{ack, packet, 0})
}

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

func (n Network) Commit(sender string) {

	for i := range n.OutboxPackets[sender] {
		n.OutboxPackets[sender][i].Commits += 1
	}
	for i := range n.OutboxAcks[sender] {
		n.OutboxAcks[sender][i].Commits += 1
	}
}
