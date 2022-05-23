// Code generated by protoc-gen-gogo. DO NOT EDIT.
// source: interchain_security/ccv/consumer/v1/consumer.proto

package types

import (
	fmt "fmt"
	types "github.com/cosmos/interchain-security/x/ccv/types"
	_ "github.com/gogo/protobuf/gogoproto"
	proto "github.com/gogo/protobuf/proto"
	io "io"
	math "math"
	math_bits "math/bits"
)

// Reference imports to suppress errors if they are not otherwise used.
var _ = proto.Marshal
var _ = fmt.Errorf
var _ = math.Inf

// This is a compile-time assertion to ensure that this generated file
// is compatible with the proto package it is being compiled against.
// A compilation error at this line likely means your copy of the
// proto package needs to be updated.
const _ = proto.GoGoProtoPackageIsVersion3 // please upgrade the proto package

// Params defines the parameters for CCV consumer module
type Params struct {
	Enabled bool `protobuf:"varint,1,opt,name=enabled,proto3" json:"enabled,omitempty"`
	///////////////////////
	// Distribution Params
	// Number of blocks between ibc-token-transfers from the consumer chain to
	// the provider chain. Note that at this transmission event a fraction of
	// the accumulated tokens are divided and sent consumer redistribution
	// address.
	BlocksPerDistributionTransmission int64 `protobuf:"varint,2,opt,name=blocks_per_distribution_transmission,json=blocksPerDistributionTransmission,proto3" json:"blocks_per_distribution_transmission,omitempty"`
	// Channel, and provider-chain receiving address to send distribution token
	// transfers over. These parameters is auto-set during the consumer <->
	// provider handshake procedure.
	DistributionTransmissionChannel string `protobuf:"bytes,3,opt,name=distribution_transmission_channel,json=distributionTransmissionChannel,proto3" json:"distribution_transmission_channel,omitempty"`
	ProviderFeePoolAddrStr          string `protobuf:"bytes,4,opt,name=provider_fee_pool_addr_str,json=providerFeePoolAddrStr,proto3" json:"provider_fee_pool_addr_str,omitempty"`
	// The fraction of tokens allocated to the consumer redistribution address
	// during distribution events. The fraction is a string representing a
	// decimal number. For example "0.5" would represent 50%.
	ConsumerRedistributeFrac string `protobuf:"bytes,5,opt,name=consumer_redistribute_frac,json=consumerRedistributeFrac,proto3" json:"consumer_redistribute_frac,omitempty"`
}

func (m *Params) Reset()         { *m = Params{} }
func (m *Params) String() string { return proto.CompactTextString(m) }
func (*Params) ProtoMessage()    {}
func (*Params) Descriptor() ([]byte, []int) {
	return fileDescriptor_5b27a82b276e7f93, []int{0}
}
func (m *Params) XXX_Unmarshal(b []byte) error {
	return m.Unmarshal(b)
}
func (m *Params) XXX_Marshal(b []byte, deterministic bool) ([]byte, error) {
	if deterministic {
		return xxx_messageInfo_Params.Marshal(b, m, deterministic)
	} else {
		b = b[:cap(b)]
		n, err := m.MarshalToSizedBuffer(b)
		if err != nil {
			return nil, err
		}
		return b[:n], nil
	}
}
func (m *Params) XXX_Merge(src proto.Message) {
	xxx_messageInfo_Params.Merge(m, src)
}
func (m *Params) XXX_Size() int {
	return m.Size()
}
func (m *Params) XXX_DiscardUnknown() {
	xxx_messageInfo_Params.DiscardUnknown(m)
}

var xxx_messageInfo_Params proto.InternalMessageInfo

func (m *Params) GetEnabled() bool {
	if m != nil {
		return m.Enabled
	}
	return false
}

func (m *Params) GetBlocksPerDistributionTransmission() int64 {
	if m != nil {
		return m.BlocksPerDistributionTransmission
	}
	return 0
}

func (m *Params) GetDistributionTransmissionChannel() string {
	if m != nil {
		return m.DistributionTransmissionChannel
	}
	return ""
}

func (m *Params) GetProviderFeePoolAddrStr() string {
	if m != nil {
		return m.ProviderFeePoolAddrStr
	}
	return ""
}

func (m *Params) GetConsumerRedistributeFrac() string {
	if m != nil {
		return m.ConsumerRedistributeFrac
	}
	return ""
}

// LastTransmissionBlockHeight is the last time validator holding
// pools were transmitted to the provider chain
type LastTransmissionBlockHeight struct {
	Height int64 `protobuf:"varint,1,opt,name=height,proto3" json:"height,omitempty"`
}

func (m *LastTransmissionBlockHeight) Reset()         { *m = LastTransmissionBlockHeight{} }
func (m *LastTransmissionBlockHeight) String() string { return proto.CompactTextString(m) }
func (*LastTransmissionBlockHeight) ProtoMessage()    {}
func (*LastTransmissionBlockHeight) Descriptor() ([]byte, []int) {
	return fileDescriptor_5b27a82b276e7f93, []int{1}
}
func (m *LastTransmissionBlockHeight) XXX_Unmarshal(b []byte) error {
	return m.Unmarshal(b)
}
func (m *LastTransmissionBlockHeight) XXX_Marshal(b []byte, deterministic bool) ([]byte, error) {
	if deterministic {
		return xxx_messageInfo_LastTransmissionBlockHeight.Marshal(b, m, deterministic)
	} else {
		b = b[:cap(b)]
		n, err := m.MarshalToSizedBuffer(b)
		if err != nil {
			return nil, err
		}
		return b[:n], nil
	}
}
func (m *LastTransmissionBlockHeight) XXX_Merge(src proto.Message) {
	xxx_messageInfo_LastTransmissionBlockHeight.Merge(m, src)
}
func (m *LastTransmissionBlockHeight) XXX_Size() int {
	return m.Size()
}
func (m *LastTransmissionBlockHeight) XXX_DiscardUnknown() {
	xxx_messageInfo_LastTransmissionBlockHeight.DiscardUnknown(m)
}

var xxx_messageInfo_LastTransmissionBlockHeight proto.InternalMessageInfo

func (m *LastTransmissionBlockHeight) GetHeight() int64 {
	if m != nil {
		return m.Height
	}
	return 0
}

// CrossChainValidator defines the validators for CCV consumer module
type CrossChainValidator struct {
	Address []byte `protobuf:"bytes,1,opt,name=address,proto3" json:"address,omitempty"`
	Power   int64  `protobuf:"varint,2,opt,name=power,proto3" json:"power,omitempty"`
}

func (m *CrossChainValidator) Reset()         { *m = CrossChainValidator{} }
func (m *CrossChainValidator) String() string { return proto.CompactTextString(m) }
func (*CrossChainValidator) ProtoMessage()    {}
func (*CrossChainValidator) Descriptor() ([]byte, []int) {
	return fileDescriptor_5b27a82b276e7f93, []int{2}
}
func (m *CrossChainValidator) XXX_Unmarshal(b []byte) error {
	return m.Unmarshal(b)
}
func (m *CrossChainValidator) XXX_Marshal(b []byte, deterministic bool) ([]byte, error) {
	if deterministic {
		return xxx_messageInfo_CrossChainValidator.Marshal(b, m, deterministic)
	} else {
		b = b[:cap(b)]
		n, err := m.MarshalToSizedBuffer(b)
		if err != nil {
			return nil, err
		}
		return b[:n], nil
	}
}
func (m *CrossChainValidator) XXX_Merge(src proto.Message) {
	xxx_messageInfo_CrossChainValidator.Merge(m, src)
}
func (m *CrossChainValidator) XXX_Size() int {
	return m.Size()
}
func (m *CrossChainValidator) XXX_DiscardUnknown() {
	xxx_messageInfo_CrossChainValidator.DiscardUnknown(m)
}

var xxx_messageInfo_CrossChainValidator proto.InternalMessageInfo

func (m *CrossChainValidator) GetAddress() []byte {
	if m != nil {
		return m.Address
	}
	return nil
}

func (m *CrossChainValidator) GetPower() int64 {
	if m != nil {
		return m.Power
	}
	return 0
}

// SlashRequest defines a slashing request for CCV consumer module
type SlashRequest struct {
	Packet   *types.SlashPacketData `protobuf:"bytes,1,opt,name=packet,proto3" json:"packet,omitempty"`
	Downtime bool                   `protobuf:"varint,2,opt,name=downtime,proto3" json:"downtime,omitempty"`
}

func (m *SlashRequest) Reset()         { *m = SlashRequest{} }
func (m *SlashRequest) String() string { return proto.CompactTextString(m) }
func (*SlashRequest) ProtoMessage()    {}
func (*SlashRequest) Descriptor() ([]byte, []int) {
	return fileDescriptor_5b27a82b276e7f93, []int{3}
}
func (m *SlashRequest) XXX_Unmarshal(b []byte) error {
	return m.Unmarshal(b)
}
func (m *SlashRequest) XXX_Marshal(b []byte, deterministic bool) ([]byte, error) {
	if deterministic {
		return xxx_messageInfo_SlashRequest.Marshal(b, m, deterministic)
	} else {
		b = b[:cap(b)]
		n, err := m.MarshalToSizedBuffer(b)
		if err != nil {
			return nil, err
		}
		return b[:n], nil
	}
}
func (m *SlashRequest) XXX_Merge(src proto.Message) {
	xxx_messageInfo_SlashRequest.Merge(m, src)
}
func (m *SlashRequest) XXX_Size() int {
	return m.Size()
}
func (m *SlashRequest) XXX_DiscardUnknown() {
	xxx_messageInfo_SlashRequest.DiscardUnknown(m)
}

var xxx_messageInfo_SlashRequest proto.InternalMessageInfo

func (m *SlashRequest) GetPacket() *types.SlashPacketData {
	if m != nil {
		return m.Packet
	}
	return nil
}

func (m *SlashRequest) GetDowntime() bool {
	if m != nil {
		return m.Downtime
	}
	return false
}

func init() {
	proto.RegisterType((*Params)(nil), "interchain_security.ccv.consumer.v1.Params")
	proto.RegisterType((*LastTransmissionBlockHeight)(nil), "interchain_security.ccv.consumer.v1.LastTransmissionBlockHeight")
	proto.RegisterType((*CrossChainValidator)(nil), "interchain_security.ccv.consumer.v1.CrossChainValidator")
	proto.RegisterType((*SlashRequest)(nil), "interchain_security.ccv.consumer.v1.SlashRequest")
}

func init() {
	proto.RegisterFile("interchain_security/ccv/consumer/v1/consumer.proto", fileDescriptor_5b27a82b276e7f93)
}

var fileDescriptor_5b27a82b276e7f93 = []byte{
	// 478 bytes of a gzipped FileDescriptorProto
	0x1f, 0x8b, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, 0xff, 0x74, 0x92, 0xc1, 0x6e, 0xd3, 0x40,
	0x10, 0x86, 0xeb, 0x86, 0x86, 0xb0, 0xf4, 0x64, 0xaa, 0xca, 0x0a, 0x92, 0x49, 0x43, 0x0f, 0x91,
	0x10, 0xb6, 0x52, 0xc4, 0xa5, 0xe2, 0x42, 0x53, 0x2a, 0x84, 0x90, 0x88, 0xdc, 0x8a, 0x03, 0x97,
	0xd5, 0x66, 0x3d, 0x8d, 0x57, 0xb5, 0x77, 0xcc, 0xec, 0xc6, 0xa5, 0x6f, 0xc1, 0xeb, 0xf0, 0x06,
	0x1c, 0x7b, 0xe4, 0x88, 0x92, 0x17, 0x41, 0x5e, 0x27, 0x21, 0x48, 0xe4, 0x36, 0xbf, 0xf5, 0xcd,
	0x3f, 0xe3, 0xd9, 0x9f, 0x9d, 0x28, 0x6d, 0x81, 0x64, 0x26, 0x94, 0xe6, 0x06, 0xe4, 0x8c, 0x94,
	0xbd, 0x8b, 0xa5, 0xac, 0x62, 0x89, 0xda, 0xcc, 0x0a, 0xa0, 0xb8, 0x1a, 0xae, 0xeb, 0xa8, 0x24,
	0xb4, 0xe8, 0x3f, 0xff, 0x4f, 0x4f, 0x24, 0x65, 0x15, 0xad, 0xb9, 0x6a, 0xd8, 0x3d, 0xde, 0x66,
	0x5c, 0xfb, 0xc9, 0xaa, 0xb1, 0xea, 0x1e, 0x4c, 0x71, 0x8a, 0xae, 0x8c, 0xeb, 0xaa, 0xf9, 0xda,
	0xff, 0xb1, 0xcb, 0xda, 0x63, 0x41, 0xa2, 0x30, 0x7e, 0xc0, 0x1e, 0x82, 0x16, 0x93, 0x1c, 0xd2,
	0xc0, 0xeb, 0x79, 0x83, 0x4e, 0xb2, 0x92, 0xfe, 0x27, 0x76, 0x3c, 0xc9, 0x51, 0xde, 0x18, 0x5e,
	0x02, 0xf1, 0x54, 0x19, 0x4b, 0x6a, 0x32, 0xb3, 0x0a, 0x35, 0xb7, 0x24, 0xb4, 0x29, 0x94, 0x31,
	0x0a, 0x75, 0xb0, 0xdb, 0xf3, 0x06, 0xad, 0xe4, 0xa8, 0x61, 0xc7, 0x40, 0xe7, 0x1b, 0xe4, 0xd5,
	0x06, 0xe8, 0x7f, 0x60, 0x47, 0x5b, 0x5d, 0xb8, 0xcc, 0x84, 0xd6, 0x90, 0x07, 0xad, 0x9e, 0x37,
	0x78, 0x94, 0x3c, 0x4b, 0xb7, 0x98, 0x8c, 0x1a, 0xcc, 0x3f, 0x65, 0xdd, 0x92, 0xb0, 0x52, 0x29,
	0x10, 0xbf, 0x06, 0xe0, 0x25, 0x62, 0xce, 0x45, 0x9a, 0x12, 0x37, 0x96, 0x82, 0x07, 0xce, 0xe4,
	0x70, 0x45, 0x5c, 0x00, 0x8c, 0x11, 0xf3, 0xb7, 0x69, 0x4a, 0x97, 0x96, 0xfc, 0x37, 0xac, 0xbb,
	0x3a, 0x24, 0x27, 0x58, 0x4f, 0x02, 0x7e, 0x4d, 0x42, 0x06, 0x7b, 0xae, 0x37, 0x58, 0x11, 0xc9,
	0x06, 0x70, 0x41, 0x42, 0xf6, 0x5f, 0xb3, 0xa7, 0x1f, 0x85, 0xb1, 0x9b, 0x4b, 0x9d, 0xd5, 0xbf,
	0xfe, 0x1e, 0xd4, 0x34, 0xb3, 0xfe, 0x21, 0x6b, 0x67, 0xae, 0x72, 0xe7, 0x6c, 0x25, 0x4b, 0xd5,
	0x7f, 0xc7, 0x9e, 0x8c, 0x08, 0x8d, 0x19, 0xd5, 0x0f, 0xf6, 0x59, 0xe4, 0x2a, 0x15, 0x16, 0xa9,
	0x3e, 0x7f, 0xbd, 0x35, 0x18, 0xe3, 0xf8, 0xfd, 0x64, 0x25, 0xfd, 0x03, 0xb6, 0x57, 0xe2, 0x2d,
	0xd0, 0xf2, 0xbe, 0x8d, 0xe8, 0x23, 0xdb, 0xbf, 0xcc, 0x85, 0xc9, 0x12, 0xf8, 0x3a, 0x03, 0x63,
	0xfd, 0x11, 0x6b, 0x97, 0x42, 0xde, 0x40, 0x33, 0xee, 0xf1, 0xc9, 0x8b, 0x68, 0x5b, 0x76, 0xaa,
	0x61, 0xe4, 0x3a, 0xc7, 0x0e, 0x3f, 0x17, 0x56, 0x24, 0xcb, 0x56, 0xbf, 0xcb, 0x3a, 0x29, 0xde,
	0x6a, 0xab, 0x0a, 0x70, 0xd3, 0x3a, 0xc9, 0x5a, 0x9f, 0x5d, 0xfd, 0x9c, 0x87, 0xde, 0xfd, 0x3c,
	0xf4, 0x7e, 0xcf, 0x43, 0xef, 0xfb, 0x22, 0xdc, 0xb9, 0x5f, 0x84, 0x3b, 0xbf, 0x16, 0xe1, 0xce,
	0x97, 0xd3, 0xa9, 0xb2, 0xd9, 0x6c, 0x12, 0x49, 0x2c, 0x62, 0x89, 0xa6, 0x40, 0x13, 0xff, 0x9d,
	0xfd, 0x72, 0x1d, 0xc9, 0x6f, 0xff, 0xa6, 0xdd, 0xde, 0x95, 0x60, 0x26, 0x6d, 0x97, 0xc3, 0x57,
	0x7f, 0x02, 0x00, 0x00, 0xff, 0xff, 0x60, 0xe8, 0x95, 0xc8, 0x1e, 0x03, 0x00, 0x00,
}

func (m *Params) Marshal() (dAtA []byte, err error) {
	size := m.Size()
	dAtA = make([]byte, size)
	n, err := m.MarshalToSizedBuffer(dAtA[:size])
	if err != nil {
		return nil, err
	}
	return dAtA[:n], nil
}

func (m *Params) MarshalTo(dAtA []byte) (int, error) {
	size := m.Size()
	return m.MarshalToSizedBuffer(dAtA[:size])
}

func (m *Params) MarshalToSizedBuffer(dAtA []byte) (int, error) {
	i := len(dAtA)
	_ = i
	var l int
	_ = l
	if len(m.ConsumerRedistributeFrac) > 0 {
		i -= len(m.ConsumerRedistributeFrac)
		copy(dAtA[i:], m.ConsumerRedistributeFrac)
		i = encodeVarintConsumer(dAtA, i, uint64(len(m.ConsumerRedistributeFrac)))
		i--
		dAtA[i] = 0x2a
	}
	if len(m.ProviderFeePoolAddrStr) > 0 {
		i -= len(m.ProviderFeePoolAddrStr)
		copy(dAtA[i:], m.ProviderFeePoolAddrStr)
		i = encodeVarintConsumer(dAtA, i, uint64(len(m.ProviderFeePoolAddrStr)))
		i--
		dAtA[i] = 0x22
	}
	if len(m.DistributionTransmissionChannel) > 0 {
		i -= len(m.DistributionTransmissionChannel)
		copy(dAtA[i:], m.DistributionTransmissionChannel)
		i = encodeVarintConsumer(dAtA, i, uint64(len(m.DistributionTransmissionChannel)))
		i--
		dAtA[i] = 0x1a
	}
	if m.BlocksPerDistributionTransmission != 0 {
		i = encodeVarintConsumer(dAtA, i, uint64(m.BlocksPerDistributionTransmission))
		i--
		dAtA[i] = 0x10
	}
	if m.Enabled {
		i--
		if m.Enabled {
			dAtA[i] = 1
		} else {
			dAtA[i] = 0
		}
		i--
		dAtA[i] = 0x8
	}
	return len(dAtA) - i, nil
}

func (m *LastTransmissionBlockHeight) Marshal() (dAtA []byte, err error) {
	size := m.Size()
	dAtA = make([]byte, size)
	n, err := m.MarshalToSizedBuffer(dAtA[:size])
	if err != nil {
		return nil, err
	}
	return dAtA[:n], nil
}

func (m *LastTransmissionBlockHeight) MarshalTo(dAtA []byte) (int, error) {
	size := m.Size()
	return m.MarshalToSizedBuffer(dAtA[:size])
}

func (m *LastTransmissionBlockHeight) MarshalToSizedBuffer(dAtA []byte) (int, error) {
	i := len(dAtA)
	_ = i
	var l int
	_ = l
	if m.Height != 0 {
		i = encodeVarintConsumer(dAtA, i, uint64(m.Height))
		i--
		dAtA[i] = 0x8
	}
	return len(dAtA) - i, nil
}

func (m *CrossChainValidator) Marshal() (dAtA []byte, err error) {
	size := m.Size()
	dAtA = make([]byte, size)
	n, err := m.MarshalToSizedBuffer(dAtA[:size])
	if err != nil {
		return nil, err
	}
	return dAtA[:n], nil
}

func (m *CrossChainValidator) MarshalTo(dAtA []byte) (int, error) {
	size := m.Size()
	return m.MarshalToSizedBuffer(dAtA[:size])
}

func (m *CrossChainValidator) MarshalToSizedBuffer(dAtA []byte) (int, error) {
	i := len(dAtA)
	_ = i
	var l int
	_ = l
	if m.Power != 0 {
		i = encodeVarintConsumer(dAtA, i, uint64(m.Power))
		i--
		dAtA[i] = 0x10
	}
	if len(m.Address) > 0 {
		i -= len(m.Address)
		copy(dAtA[i:], m.Address)
		i = encodeVarintConsumer(dAtA, i, uint64(len(m.Address)))
		i--
		dAtA[i] = 0xa
	}
	return len(dAtA) - i, nil
}

func (m *SlashRequest) Marshal() (dAtA []byte, err error) {
	size := m.Size()
	dAtA = make([]byte, size)
	n, err := m.MarshalToSizedBuffer(dAtA[:size])
	if err != nil {
		return nil, err
	}
	return dAtA[:n], nil
}

func (m *SlashRequest) MarshalTo(dAtA []byte) (int, error) {
	size := m.Size()
	return m.MarshalToSizedBuffer(dAtA[:size])
}

func (m *SlashRequest) MarshalToSizedBuffer(dAtA []byte) (int, error) {
	i := len(dAtA)
	_ = i
	var l int
	_ = l
	if m.Downtime {
		i--
		if m.Downtime {
			dAtA[i] = 1
		} else {
			dAtA[i] = 0
		}
		i--
		dAtA[i] = 0x10
	}
	if m.Packet != nil {
		{
			size, err := m.Packet.MarshalToSizedBuffer(dAtA[:i])
			if err != nil {
				return 0, err
			}
			i -= size
			i = encodeVarintConsumer(dAtA, i, uint64(size))
		}
		i--
		dAtA[i] = 0xa
	}
	return len(dAtA) - i, nil
}

func encodeVarintConsumer(dAtA []byte, offset int, v uint64) int {
	offset -= sovConsumer(v)
	base := offset
	for v >= 1<<7 {
		dAtA[offset] = uint8(v&0x7f | 0x80)
		v >>= 7
		offset++
	}
	dAtA[offset] = uint8(v)
	return base
}
func (m *Params) Size() (n int) {
	if m == nil {
		return 0
	}
	var l int
	_ = l
	if m.Enabled {
		n += 2
	}
	if m.BlocksPerDistributionTransmission != 0 {
		n += 1 + sovConsumer(uint64(m.BlocksPerDistributionTransmission))
	}
	l = len(m.DistributionTransmissionChannel)
	if l > 0 {
		n += 1 + l + sovConsumer(uint64(l))
	}
	l = len(m.ProviderFeePoolAddrStr)
	if l > 0 {
		n += 1 + l + sovConsumer(uint64(l))
	}
	l = len(m.ConsumerRedistributeFrac)
	if l > 0 {
		n += 1 + l + sovConsumer(uint64(l))
	}
	return n
}

func (m *LastTransmissionBlockHeight) Size() (n int) {
	if m == nil {
		return 0
	}
	var l int
	_ = l
	if m.Height != 0 {
		n += 1 + sovConsumer(uint64(m.Height))
	}
	return n
}

func (m *CrossChainValidator) Size() (n int) {
	if m == nil {
		return 0
	}
	var l int
	_ = l
	l = len(m.Address)
	if l > 0 {
		n += 1 + l + sovConsumer(uint64(l))
	}
	if m.Power != 0 {
		n += 1 + sovConsumer(uint64(m.Power))
	}
	return n
}

func (m *SlashRequest) Size() (n int) {
	if m == nil {
		return 0
	}
	var l int
	_ = l
	if m.Packet != nil {
		l = m.Packet.Size()
		n += 1 + l + sovConsumer(uint64(l))
	}
	if m.Downtime {
		n += 2
	}
	return n
}

func sovConsumer(x uint64) (n int) {
	return (math_bits.Len64(x|1) + 6) / 7
}
func sozConsumer(x uint64) (n int) {
	return sovConsumer(uint64((x << 1) ^ uint64((int64(x) >> 63))))
}
func (m *Params) Unmarshal(dAtA []byte) error {
	l := len(dAtA)
	iNdEx := 0
	for iNdEx < l {
		preIndex := iNdEx
		var wire uint64
		for shift := uint(0); ; shift += 7 {
			if shift >= 64 {
				return ErrIntOverflowConsumer
			}
			if iNdEx >= l {
				return io.ErrUnexpectedEOF
			}
			b := dAtA[iNdEx]
			iNdEx++
			wire |= uint64(b&0x7F) << shift
			if b < 0x80 {
				break
			}
		}
		fieldNum := int32(wire >> 3)
		wireType := int(wire & 0x7)
		if wireType == 4 {
			return fmt.Errorf("proto: Params: wiretype end group for non-group")
		}
		if fieldNum <= 0 {
			return fmt.Errorf("proto: Params: illegal tag %d (wire type %d)", fieldNum, wire)
		}
		switch fieldNum {
		case 1:
			if wireType != 0 {
				return fmt.Errorf("proto: wrong wireType = %d for field Enabled", wireType)
			}
			var v int
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowConsumer
				}
				if iNdEx >= l {
					return io.ErrUnexpectedEOF
				}
				b := dAtA[iNdEx]
				iNdEx++
				v |= int(b&0x7F) << shift
				if b < 0x80 {
					break
				}
			}
			m.Enabled = bool(v != 0)
		case 2:
			if wireType != 0 {
				return fmt.Errorf("proto: wrong wireType = %d for field BlocksPerDistributionTransmission", wireType)
			}
			m.BlocksPerDistributionTransmission = 0
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowConsumer
				}
				if iNdEx >= l {
					return io.ErrUnexpectedEOF
				}
				b := dAtA[iNdEx]
				iNdEx++
				m.BlocksPerDistributionTransmission |= int64(b&0x7F) << shift
				if b < 0x80 {
					break
				}
			}
		case 3:
			if wireType != 2 {
				return fmt.Errorf("proto: wrong wireType = %d for field DistributionTransmissionChannel", wireType)
			}
			var stringLen uint64
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowConsumer
				}
				if iNdEx >= l {
					return io.ErrUnexpectedEOF
				}
				b := dAtA[iNdEx]
				iNdEx++
				stringLen |= uint64(b&0x7F) << shift
				if b < 0x80 {
					break
				}
			}
			intStringLen := int(stringLen)
			if intStringLen < 0 {
				return ErrInvalidLengthConsumer
			}
			postIndex := iNdEx + intStringLen
			if postIndex < 0 {
				return ErrInvalidLengthConsumer
			}
			if postIndex > l {
				return io.ErrUnexpectedEOF
			}
			m.DistributionTransmissionChannel = string(dAtA[iNdEx:postIndex])
			iNdEx = postIndex
		case 4:
			if wireType != 2 {
				return fmt.Errorf("proto: wrong wireType = %d for field ProviderFeePoolAddrStr", wireType)
			}
			var stringLen uint64
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowConsumer
				}
				if iNdEx >= l {
					return io.ErrUnexpectedEOF
				}
				b := dAtA[iNdEx]
				iNdEx++
				stringLen |= uint64(b&0x7F) << shift
				if b < 0x80 {
					break
				}
			}
			intStringLen := int(stringLen)
			if intStringLen < 0 {
				return ErrInvalidLengthConsumer
			}
			postIndex := iNdEx + intStringLen
			if postIndex < 0 {
				return ErrInvalidLengthConsumer
			}
			if postIndex > l {
				return io.ErrUnexpectedEOF
			}
			m.ProviderFeePoolAddrStr = string(dAtA[iNdEx:postIndex])
			iNdEx = postIndex
		case 5:
			if wireType != 2 {
				return fmt.Errorf("proto: wrong wireType = %d for field ConsumerRedistributeFrac", wireType)
			}
			var stringLen uint64
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowConsumer
				}
				if iNdEx >= l {
					return io.ErrUnexpectedEOF
				}
				b := dAtA[iNdEx]
				iNdEx++
				stringLen |= uint64(b&0x7F) << shift
				if b < 0x80 {
					break
				}
			}
			intStringLen := int(stringLen)
			if intStringLen < 0 {
				return ErrInvalidLengthConsumer
			}
			postIndex := iNdEx + intStringLen
			if postIndex < 0 {
				return ErrInvalidLengthConsumer
			}
			if postIndex > l {
				return io.ErrUnexpectedEOF
			}
			m.ConsumerRedistributeFrac = string(dAtA[iNdEx:postIndex])
			iNdEx = postIndex
		default:
			iNdEx = preIndex
			skippy, err := skipConsumer(dAtA[iNdEx:])
			if err != nil {
				return err
			}
			if (skippy < 0) || (iNdEx+skippy) < 0 {
				return ErrInvalidLengthConsumer
			}
			if (iNdEx + skippy) > l {
				return io.ErrUnexpectedEOF
			}
			iNdEx += skippy
		}
	}

	if iNdEx > l {
		return io.ErrUnexpectedEOF
	}
	return nil
}
func (m *LastTransmissionBlockHeight) Unmarshal(dAtA []byte) error {
	l := len(dAtA)
	iNdEx := 0
	for iNdEx < l {
		preIndex := iNdEx
		var wire uint64
		for shift := uint(0); ; shift += 7 {
			if shift >= 64 {
				return ErrIntOverflowConsumer
			}
			if iNdEx >= l {
				return io.ErrUnexpectedEOF
			}
			b := dAtA[iNdEx]
			iNdEx++
			wire |= uint64(b&0x7F) << shift
			if b < 0x80 {
				break
			}
		}
		fieldNum := int32(wire >> 3)
		wireType := int(wire & 0x7)
		if wireType == 4 {
			return fmt.Errorf("proto: LastTransmissionBlockHeight: wiretype end group for non-group")
		}
		if fieldNum <= 0 {
			return fmt.Errorf("proto: LastTransmissionBlockHeight: illegal tag %d (wire type %d)", fieldNum, wire)
		}
		switch fieldNum {
		case 1:
			if wireType != 0 {
				return fmt.Errorf("proto: wrong wireType = %d for field Height", wireType)
			}
			m.Height = 0
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowConsumer
				}
				if iNdEx >= l {
					return io.ErrUnexpectedEOF
				}
				b := dAtA[iNdEx]
				iNdEx++
				m.Height |= int64(b&0x7F) << shift
				if b < 0x80 {
					break
				}
			}
		default:
			iNdEx = preIndex
			skippy, err := skipConsumer(dAtA[iNdEx:])
			if err != nil {
				return err
			}
			if (skippy < 0) || (iNdEx+skippy) < 0 {
				return ErrInvalidLengthConsumer
			}
			if (iNdEx + skippy) > l {
				return io.ErrUnexpectedEOF
			}
			iNdEx += skippy
		}
	}

	if iNdEx > l {
		return io.ErrUnexpectedEOF
	}
	return nil
}
func (m *CrossChainValidator) Unmarshal(dAtA []byte) error {
	l := len(dAtA)
	iNdEx := 0
	for iNdEx < l {
		preIndex := iNdEx
		var wire uint64
		for shift := uint(0); ; shift += 7 {
			if shift >= 64 {
				return ErrIntOverflowConsumer
			}
			if iNdEx >= l {
				return io.ErrUnexpectedEOF
			}
			b := dAtA[iNdEx]
			iNdEx++
			wire |= uint64(b&0x7F) << shift
			if b < 0x80 {
				break
			}
		}
		fieldNum := int32(wire >> 3)
		wireType := int(wire & 0x7)
		if wireType == 4 {
			return fmt.Errorf("proto: CrossChainValidator: wiretype end group for non-group")
		}
		if fieldNum <= 0 {
			return fmt.Errorf("proto: CrossChainValidator: illegal tag %d (wire type %d)", fieldNum, wire)
		}
		switch fieldNum {
		case 1:
			if wireType != 2 {
				return fmt.Errorf("proto: wrong wireType = %d for field Address", wireType)
			}
			var byteLen int
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowConsumer
				}
				if iNdEx >= l {
					return io.ErrUnexpectedEOF
				}
				b := dAtA[iNdEx]
				iNdEx++
				byteLen |= int(b&0x7F) << shift
				if b < 0x80 {
					break
				}
			}
			if byteLen < 0 {
				return ErrInvalidLengthConsumer
			}
			postIndex := iNdEx + byteLen
			if postIndex < 0 {
				return ErrInvalidLengthConsumer
			}
			if postIndex > l {
				return io.ErrUnexpectedEOF
			}
			m.Address = append(m.Address[:0], dAtA[iNdEx:postIndex]...)
			if m.Address == nil {
				m.Address = []byte{}
			}
			iNdEx = postIndex
		case 2:
			if wireType != 0 {
				return fmt.Errorf("proto: wrong wireType = %d for field Power", wireType)
			}
			m.Power = 0
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowConsumer
				}
				if iNdEx >= l {
					return io.ErrUnexpectedEOF
				}
				b := dAtA[iNdEx]
				iNdEx++
				m.Power |= int64(b&0x7F) << shift
				if b < 0x80 {
					break
				}
			}
		default:
			iNdEx = preIndex
			skippy, err := skipConsumer(dAtA[iNdEx:])
			if err != nil {
				return err
			}
			if (skippy < 0) || (iNdEx+skippy) < 0 {
				return ErrInvalidLengthConsumer
			}
			if (iNdEx + skippy) > l {
				return io.ErrUnexpectedEOF
			}
			iNdEx += skippy
		}
	}

	if iNdEx > l {
		return io.ErrUnexpectedEOF
	}
	return nil
}
func (m *SlashRequest) Unmarshal(dAtA []byte) error {
	l := len(dAtA)
	iNdEx := 0
	for iNdEx < l {
		preIndex := iNdEx
		var wire uint64
		for shift := uint(0); ; shift += 7 {
			if shift >= 64 {
				return ErrIntOverflowConsumer
			}
			if iNdEx >= l {
				return io.ErrUnexpectedEOF
			}
			b := dAtA[iNdEx]
			iNdEx++
			wire |= uint64(b&0x7F) << shift
			if b < 0x80 {
				break
			}
		}
		fieldNum := int32(wire >> 3)
		wireType := int(wire & 0x7)
		if wireType == 4 {
			return fmt.Errorf("proto: SlashRequest: wiretype end group for non-group")
		}
		if fieldNum <= 0 {
			return fmt.Errorf("proto: SlashRequest: illegal tag %d (wire type %d)", fieldNum, wire)
		}
		switch fieldNum {
		case 1:
			if wireType != 2 {
				return fmt.Errorf("proto: wrong wireType = %d for field Packet", wireType)
			}
			var msglen int
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowConsumer
				}
				if iNdEx >= l {
					return io.ErrUnexpectedEOF
				}
				b := dAtA[iNdEx]
				iNdEx++
				msglen |= int(b&0x7F) << shift
				if b < 0x80 {
					break
				}
			}
			if msglen < 0 {
				return ErrInvalidLengthConsumer
			}
			postIndex := iNdEx + msglen
			if postIndex < 0 {
				return ErrInvalidLengthConsumer
			}
			if postIndex > l {
				return io.ErrUnexpectedEOF
			}
			if m.Packet == nil {
				m.Packet = &types.SlashPacketData{}
			}
			if err := m.Packet.Unmarshal(dAtA[iNdEx:postIndex]); err != nil {
				return err
			}
			iNdEx = postIndex
		case 2:
			if wireType != 0 {
				return fmt.Errorf("proto: wrong wireType = %d for field Downtime", wireType)
			}
			var v int
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowConsumer
				}
				if iNdEx >= l {
					return io.ErrUnexpectedEOF
				}
				b := dAtA[iNdEx]
				iNdEx++
				v |= int(b&0x7F) << shift
				if b < 0x80 {
					break
				}
			}
			m.Downtime = bool(v != 0)
		default:
			iNdEx = preIndex
			skippy, err := skipConsumer(dAtA[iNdEx:])
			if err != nil {
				return err
			}
			if (skippy < 0) || (iNdEx+skippy) < 0 {
				return ErrInvalidLengthConsumer
			}
			if (iNdEx + skippy) > l {
				return io.ErrUnexpectedEOF
			}
			iNdEx += skippy
		}
	}

	if iNdEx > l {
		return io.ErrUnexpectedEOF
	}
	return nil
}
func skipConsumer(dAtA []byte) (n int, err error) {
	l := len(dAtA)
	iNdEx := 0
	depth := 0
	for iNdEx < l {
		var wire uint64
		for shift := uint(0); ; shift += 7 {
			if shift >= 64 {
				return 0, ErrIntOverflowConsumer
			}
			if iNdEx >= l {
				return 0, io.ErrUnexpectedEOF
			}
			b := dAtA[iNdEx]
			iNdEx++
			wire |= (uint64(b) & 0x7F) << shift
			if b < 0x80 {
				break
			}
		}
		wireType := int(wire & 0x7)
		switch wireType {
		case 0:
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return 0, ErrIntOverflowConsumer
				}
				if iNdEx >= l {
					return 0, io.ErrUnexpectedEOF
				}
				iNdEx++
				if dAtA[iNdEx-1] < 0x80 {
					break
				}
			}
		case 1:
			iNdEx += 8
		case 2:
			var length int
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return 0, ErrIntOverflowConsumer
				}
				if iNdEx >= l {
					return 0, io.ErrUnexpectedEOF
				}
				b := dAtA[iNdEx]
				iNdEx++
				length |= (int(b) & 0x7F) << shift
				if b < 0x80 {
					break
				}
			}
			if length < 0 {
				return 0, ErrInvalidLengthConsumer
			}
			iNdEx += length
		case 3:
			depth++
		case 4:
			if depth == 0 {
				return 0, ErrUnexpectedEndOfGroupConsumer
			}
			depth--
		case 5:
			iNdEx += 4
		default:
			return 0, fmt.Errorf("proto: illegal wireType %d", wireType)
		}
		if iNdEx < 0 {
			return 0, ErrInvalidLengthConsumer
		}
		if depth == 0 {
			return iNdEx, nil
		}
	}
	return 0, io.ErrUnexpectedEOF
}

var (
	ErrInvalidLengthConsumer        = fmt.Errorf("proto: negative length found during unmarshaling")
	ErrIntOverflowConsumer          = fmt.Errorf("proto: integer overflow")
	ErrUnexpectedEndOfGroupConsumer = fmt.Errorf("proto: unexpected end of group")
)
