// Code generated by protoc-gen-gogo. DO NOT EDIT.
// source: interchain_security/ccv/consumer/v1/consumer.proto

package types

import (
	fmt "fmt"
	types "github.com/cosmos/cosmos-sdk/codec/types"
	types2 "github.com/cosmos/cosmos-sdk/x/staking/types"
	types1 "github.com/cosmos/interchain-security/x/ccv/types"
	_ "github.com/gogo/protobuf/gogoproto"
	proto "github.com/gogo/protobuf/proto"
	_ "github.com/regen-network/cosmos-proto"
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
	// pubkey is the consensus public key of the validator, as a Protobuf Any.
	Pubkey *types.Any `protobuf:"bytes,3,opt,name=pubkey,proto3" json:"pubkey,omitempty" yaml:"consensus_pubkey"`
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

func (m *CrossChainValidator) GetPubkey() *types.Any {
	if m != nil {
		return m.Pubkey
	}
	return nil
}

// SlashRequest defines a slashing request for CCV consumer module
type SlashRequest struct {
	Packet     *types1.SlashPacketData `protobuf:"bytes,1,opt,name=packet,proto3" json:"packet,omitempty"`
	Infraction types2.InfractionType   `protobuf:"varint,2,opt,name=infraction,proto3,enum=cosmos.staking.v1beta1.InfractionType" json:"infraction,omitempty"`
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

func (m *SlashRequest) GetPacket() *types1.SlashPacketData {
	if m != nil {
		return m.Packet
	}
	return nil
}

func (m *SlashRequest) GetInfraction() types2.InfractionType {
	if m != nil {
		return m.Infraction
	}
	return types2.InfractionEmpty
}

// SlashRequests is a list of slash requests for CCV consumer module
type SlashRequests struct {
	Requests []SlashRequest `protobuf:"bytes,1,rep,name=requests,proto3" json:"requests"`
}

func (m *SlashRequests) Reset()         { *m = SlashRequests{} }
func (m *SlashRequests) String() string { return proto.CompactTextString(m) }
func (*SlashRequests) ProtoMessage()    {}
func (*SlashRequests) Descriptor() ([]byte, []int) {
	return fileDescriptor_5b27a82b276e7f93, []int{4}
}
func (m *SlashRequests) XXX_Unmarshal(b []byte) error {
	return m.Unmarshal(b)
}
func (m *SlashRequests) XXX_Marshal(b []byte, deterministic bool) ([]byte, error) {
	if deterministic {
		return xxx_messageInfo_SlashRequests.Marshal(b, m, deterministic)
	} else {
		b = b[:cap(b)]
		n, err := m.MarshalToSizedBuffer(b)
		if err != nil {
			return nil, err
		}
		return b[:n], nil
	}
}
func (m *SlashRequests) XXX_Merge(src proto.Message) {
	xxx_messageInfo_SlashRequests.Merge(m, src)
}
func (m *SlashRequests) XXX_Size() int {
	return m.Size()
}
func (m *SlashRequests) XXX_DiscardUnknown() {
	xxx_messageInfo_SlashRequests.DiscardUnknown(m)
}

var xxx_messageInfo_SlashRequests proto.InternalMessageInfo

func (m *SlashRequests) GetRequests() []SlashRequest {
	if m != nil {
		return m.Requests
	}
	return nil
}

func init() {
	proto.RegisterType((*Params)(nil), "interchain_security.ccv.consumer.v1.Params")
	proto.RegisterType((*LastTransmissionBlockHeight)(nil), "interchain_security.ccv.consumer.v1.LastTransmissionBlockHeight")
	proto.RegisterType((*CrossChainValidator)(nil), "interchain_security.ccv.consumer.v1.CrossChainValidator")
	proto.RegisterType((*SlashRequest)(nil), "interchain_security.ccv.consumer.v1.SlashRequest")
	proto.RegisterType((*SlashRequests)(nil), "interchain_security.ccv.consumer.v1.SlashRequests")
}

func init() {
	proto.RegisterFile("interchain_security/ccv/consumer/v1/consumer.proto", fileDescriptor_5b27a82b276e7f93)
}

var fileDescriptor_5b27a82b276e7f93 = []byte{
	// 614 bytes of a gzipped FileDescriptorProto
	0x1f, 0x8b, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, 0xff, 0x8c, 0x54, 0xcd, 0x6e, 0xd3, 0x4c,
	0x14, 0x8d, 0xbf, 0xf4, 0x0b, 0x65, 0x5a, 0x58, 0x98, 0xa8, 0x84, 0x22, 0xa5, 0xa9, 0xa9, 0x50,
	0x24, 0xd4, 0xb1, 0x92, 0x8a, 0x4d, 0x77, 0x4d, 0xaa, 0x8a, 0x3f, 0x89, 0xc8, 0xad, 0x58, 0xb0,
	0xb1, 0xc6, 0xe3, 0x5b, 0x67, 0x14, 0x7b, 0xc6, 0xcc, 0x8c, 0x0d, 0x7e, 0x0b, 0xf6, 0xbc, 0x00,
	0x0f, 0xc0, 0x43, 0x54, 0xac, 0xba, 0x64, 0x55, 0xa1, 0xf6, 0x0d, 0xd8, 0xb2, 0x41, 0xfe, 0x0b,
	0x46, 0x22, 0x12, 0xbb, 0x7b, 0x34, 0xe7, 0x1c, 0xcf, 0xdc, 0x73, 0xaf, 0xd1, 0x98, 0x71, 0x0d,
	0x92, 0xce, 0x09, 0xe3, 0xae, 0x02, 0x9a, 0x48, 0xa6, 0x33, 0x9b, 0xd2, 0xd4, 0xa6, 0x82, 0xab,
	0x24, 0x02, 0x69, 0xa7, 0xa3, 0x65, 0x8d, 0x63, 0x29, 0xb4, 0x30, 0x1f, 0xfd, 0x45, 0x83, 0x29,
	0x4d, 0xf1, 0x92, 0x97, 0x8e, 0xb6, 0xf7, 0x56, 0x19, 0xe7, 0x7e, 0x34, 0x2d, 0xad, 0xb6, 0x1f,
	0x04, 0x42, 0x04, 0x21, 0xd8, 0x05, 0xf2, 0x92, 0x73, 0x9b, 0xf0, 0xac, 0x3a, 0xda, 0xa3, 0x42,
	0x45, 0x42, 0xd9, 0x4a, 0x93, 0x05, 0xe3, 0x81, 0x9d, 0x8e, 0x3c, 0xd0, 0x64, 0x54, 0xe3, 0x8a,
	0xd5, 0x0d, 0x44, 0x20, 0x8a, 0xd2, 0xce, 0xab, 0xda, 0xb6, 0xd4, 0xba, 0xe5, 0x41, 0x09, 0xca,
	0x23, 0xeb, 0xa7, 0x81, 0x3a, 0x33, 0x22, 0x49, 0xa4, 0xcc, 0x1e, 0xba, 0x05, 0x9c, 0x78, 0x21,
	0xf8, 0x3d, 0x63, 0x60, 0x0c, 0xd7, 0x9d, 0x1a, 0x9a, 0xaf, 0xd1, 0x9e, 0x17, 0x0a, 0xba, 0x50,
	0x6e, 0x0c, 0xd2, 0xf5, 0x99, 0xd2, 0x92, 0x79, 0x89, 0x66, 0x82, 0xbb, 0x5a, 0x12, 0xae, 0x22,
	0xa6, 0x14, 0x13, 0xbc, 0xf7, 0xdf, 0xc0, 0x18, 0xb6, 0x9d, 0xdd, 0x92, 0x3b, 0x03, 0x79, 0xdc,
	0x60, 0x9e, 0x35, 0x88, 0xe6, 0x0b, 0xb4, 0xbb, 0xd2, 0xc5, 0xa5, 0x73, 0xc2, 0x39, 0x84, 0xbd,
	0xf6, 0xc0, 0x18, 0xde, 0x76, 0x76, 0xfc, 0x15, 0x26, 0xd3, 0x92, 0x66, 0x1e, 0xa2, 0xed, 0x58,
	0x8a, 0x94, 0xf9, 0x20, 0xdd, 0x73, 0x00, 0x37, 0x16, 0x22, 0x74, 0x89, 0xef, 0x4b, 0x57, 0x69,
	0xd9, 0x5b, 0x2b, 0x4c, 0xb6, 0x6a, 0xc6, 0x09, 0xc0, 0x4c, 0x88, 0xf0, 0xc8, 0xf7, 0xe5, 0xa9,
	0x96, 0xd6, 0x53, 0xf4, 0xf0, 0x15, 0x51, 0xba, 0x69, 0x3b, 0xc9, 0x2f, 0xff, 0x0c, 0x58, 0x30,
	0xd7, 0xe6, 0x16, 0xea, 0xcc, 0x8b, 0xaa, 0x68, 0x48, 0xdb, 0xa9, 0x90, 0xf5, 0xd9, 0x40, 0xf7,
	0xa6, 0x52, 0x28, 0x35, 0xcd, 0xf3, 0x7c, 0x43, 0x42, 0xe6, 0x13, 0x2d, 0x64, 0xde, 0xc1, 0xfc,
	0xc3, 0xa0, 0x54, 0x21, 0xd8, 0x74, 0x6a, 0x68, 0x76, 0xd1, 0xff, 0xb1, 0x78, 0x0f, 0xb2, 0x6a,
	0x51, 0x09, 0x4c, 0x82, 0x3a, 0x71, 0xe2, 0x2d, 0x20, 0x2b, 0xde, 0xba, 0x31, 0xee, 0xe2, 0x32,
	0x7f, 0x5c, 0xe7, 0x8f, 0x8f, 0x78, 0x36, 0x39, 0xf8, 0x71, 0xb5, 0x73, 0x3f, 0x23, 0x51, 0x78,
	0x68, 0xe5, 0x13, 0x05, 0x5c, 0x25, 0xca, 0x2d, 0x75, 0xd6, 0xd7, 0x2f, 0xfb, 0xdd, 0x2a, 0x4f,
	0x2a, 0xb3, 0x58, 0x0b, 0x3c, 0x4b, 0xbc, 0x97, 0x90, 0x39, 0x95, 0xb1, 0xf5, 0xc9, 0x40, 0x9b,
	0xa7, 0x21, 0x51, 0x73, 0x07, 0xde, 0x25, 0xa0, 0xb4, 0x39, 0x45, 0x9d, 0x98, 0xd0, 0x05, 0x94,
	0x6f, 0xda, 0x18, 0x3f, 0xc1, 0xab, 0xc6, 0x37, 0x1d, 0xe1, 0x42, 0x39, 0x2b, 0xe8, 0xc7, 0x44,
	0x13, 0xa7, 0x92, 0x9a, 0x27, 0x08, 0x31, 0x7e, 0x2e, 0x09, 0xd5, 0x75, 0xec, 0x77, 0xc7, 0x8f,
	0x71, 0x75, 0x91, 0x7a, 0x22, 0xab, 0x09, 0xc5, 0xcf, 0x97, 0xcc, 0xb3, 0x2c, 0x06, 0xa7, 0xa1,
	0xb4, 0x7c, 0x74, 0xa7, 0x79, 0x39, 0x65, 0x9e, 0xa2, 0x75, 0x59, 0xd5, 0x3d, 0x63, 0xd0, 0x1e,
	0x6e, 0x8c, 0x47, 0xf8, 0x1f, 0xd6, 0x0b, 0x37, 0x5d, 0x26, 0x6b, 0x17, 0x57, 0x3b, 0x2d, 0x67,
	0x69, 0x34, 0x39, 0xbb, 0xb8, 0xee, 0x1b, 0x97, 0xd7, 0x7d, 0xe3, 0xfb, 0x75, 0xdf, 0xf8, 0x78,
	0xd3, 0x6f, 0x5d, 0xde, 0xf4, 0x5b, 0xdf, 0x6e, 0xfa, 0xad, 0xb7, 0x87, 0x01, 0xd3, 0xf3, 0xc4,
	0xc3, 0x54, 0x44, 0xd5, 0x5a, 0xd8, 0xbf, 0xbf, 0xb6, 0xbf, 0xdc, 0xd3, 0x0f, 0x7f, 0xfe, 0x02,
	0x74, 0x16, 0x83, 0xf2, 0x3a, 0x45, 0x48, 0x07, 0xbf, 0x02, 0x00, 0x00, 0xff, 0xff, 0x91, 0xef,
	0xc0, 0x3c, 0x33, 0x04, 0x00, 0x00,
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
	if m.Pubkey != nil {
		{
			size, err := m.Pubkey.MarshalToSizedBuffer(dAtA[:i])
			if err != nil {
				return 0, err
			}
			i -= size
			i = encodeVarintConsumer(dAtA, i, uint64(size))
		}
		i--
		dAtA[i] = 0x1a
	}
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
	if m.Infraction != 0 {
		i = encodeVarintConsumer(dAtA, i, uint64(m.Infraction))
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

func (m *SlashRequests) Marshal() (dAtA []byte, err error) {
	size := m.Size()
	dAtA = make([]byte, size)
	n, err := m.MarshalToSizedBuffer(dAtA[:size])
	if err != nil {
		return nil, err
	}
	return dAtA[:n], nil
}

func (m *SlashRequests) MarshalTo(dAtA []byte) (int, error) {
	size := m.Size()
	return m.MarshalToSizedBuffer(dAtA[:size])
}

func (m *SlashRequests) MarshalToSizedBuffer(dAtA []byte) (int, error) {
	i := len(dAtA)
	_ = i
	var l int
	_ = l
	if len(m.Requests) > 0 {
		for iNdEx := len(m.Requests) - 1; iNdEx >= 0; iNdEx-- {
			{
				size, err := m.Requests[iNdEx].MarshalToSizedBuffer(dAtA[:i])
				if err != nil {
					return 0, err
				}
				i -= size
				i = encodeVarintConsumer(dAtA, i, uint64(size))
			}
			i--
			dAtA[i] = 0xa
		}
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
	if m.Pubkey != nil {
		l = m.Pubkey.Size()
		n += 1 + l + sovConsumer(uint64(l))
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
	if m.Infraction != 0 {
		n += 1 + sovConsumer(uint64(m.Infraction))
	}
	return n
}

func (m *SlashRequests) Size() (n int) {
	if m == nil {
		return 0
	}
	var l int
	_ = l
	if len(m.Requests) > 0 {
		for _, e := range m.Requests {
			l = e.Size()
			n += 1 + l + sovConsumer(uint64(l))
		}
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
		case 3:
			if wireType != 2 {
				return fmt.Errorf("proto: wrong wireType = %d for field Pubkey", wireType)
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
			if m.Pubkey == nil {
				m.Pubkey = &types.Any{}
			}
			if err := m.Pubkey.Unmarshal(dAtA[iNdEx:postIndex]); err != nil {
				return err
			}
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
				m.Packet = &types1.SlashPacketData{}
			}
			if err := m.Packet.Unmarshal(dAtA[iNdEx:postIndex]); err != nil {
				return err
			}
			iNdEx = postIndex
		case 2:
			if wireType != 0 {
				return fmt.Errorf("proto: wrong wireType = %d for field Infraction", wireType)
			}
			m.Infraction = 0
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowConsumer
				}
				if iNdEx >= l {
					return io.ErrUnexpectedEOF
				}
				b := dAtA[iNdEx]
				iNdEx++
				m.Infraction |= types2.InfractionType(b&0x7F) << shift
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
func (m *SlashRequests) Unmarshal(dAtA []byte) error {
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
			return fmt.Errorf("proto: SlashRequests: wiretype end group for non-group")
		}
		if fieldNum <= 0 {
			return fmt.Errorf("proto: SlashRequests: illegal tag %d (wire type %d)", fieldNum, wire)
		}
		switch fieldNum {
		case 1:
			if wireType != 2 {
				return fmt.Errorf("proto: wrong wireType = %d for field Requests", wireType)
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
			m.Requests = append(m.Requests, SlashRequest{})
			if err := m.Requests[len(m.Requests)-1].Unmarshal(dAtA[iNdEx:postIndex]); err != nil {
				return err
			}
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
