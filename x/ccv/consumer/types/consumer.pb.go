// Code generated by protoc-gen-gogo. DO NOT EDIT.
// source: interchain_security/ccv/consumer/v1/consumer.proto

package types

import (
	fmt "fmt"
	types "github.com/cosmos/cosmos-sdk/codec/types"
	_ "github.com/cosmos/interchain-security/x/ccv/types"
	_ "github.com/gogo/protobuf/gogoproto"
	proto "github.com/gogo/protobuf/proto"
	github_com_gogo_protobuf_types "github.com/gogo/protobuf/types"
	_ "github.com/regen-network/cosmos-proto"
	_ "google.golang.org/protobuf/types/known/durationpb"
	_ "google.golang.org/protobuf/types/known/timestamppb"
	io "io"
	math "math"
	math_bits "math/bits"
	time "time"
)

// Reference imports to suppress errors if they are not otherwise used.
var _ = proto.Marshal
var _ = fmt.Errorf
var _ = math.Inf
var _ = time.Kitchen

// This is a compile-time assertion to ensure that this generated file
// is compatible with the proto package it is being compiled against.
// A compilation error at this line likely means your copy of the
// proto package needs to be updated.
const _ = proto.GoGoProtoPackageIsVersion3 // please upgrade the proto package

// Params defines the parameters for CCV consumer module
type Params struct {
	// TODO: Remove enabled flag and find a better way to setup e2e tests
	// See: https://github.com/cosmos/interchain-security/issues/339
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
	// Sent CCV related IBC packets will timeout after this duration
	CcvTimeoutPeriod time.Duration `protobuf:"bytes,5,opt,name=ccv_timeout_period,json=ccvTimeoutPeriod,proto3,stdduration" json:"ccv_timeout_period"`
	// Sent transfer related IBC packets will timeout after this duration
	TransferTimeoutPeriod time.Duration `protobuf:"bytes,6,opt,name=transfer_timeout_period,json=transferTimeoutPeriod,proto3,stdduration" json:"transfer_timeout_period"`
	// The fraction of tokens allocated to the consumer redistribution address
	// during distribution events. The fraction is a string representing a
	// decimal number. For example "0.75" would represent 75%.
	ConsumerRedistributionFraction string `protobuf:"bytes,7,opt,name=consumer_redistribution_fraction,json=consumerRedistributionFraction,proto3" json:"consumer_redistribution_fraction,omitempty"`
	// The number of historical info entries to persist in store.
	// This param is a part of the cosmos sdk staking module. In the case of
	// a ccv enabled consumer chain, the ccv module acts as the staking module.
	HistoricalEntries int64 `protobuf:"varint,8,opt,name=historical_entries,json=historicalEntries,proto3" json:"historical_entries,omitempty"`
	// Unbonding period for the consumer,
	// which should be smaller than that of the provider in general.
	UnbondingPeriod time.Duration `protobuf:"bytes,9,opt,name=unbonding_period,json=unbondingPeriod,proto3,stdduration" json:"unbonding_period"`
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

func (m *Params) GetCcvTimeoutPeriod() time.Duration {
	if m != nil {
		return m.CcvTimeoutPeriod
	}
	return 0
}

func (m *Params) GetTransferTimeoutPeriod() time.Duration {
	if m != nil {
		return m.TransferTimeoutPeriod
	}
	return 0
}

func (m *Params) GetConsumerRedistributionFraction() string {
	if m != nil {
		return m.ConsumerRedistributionFraction
	}
	return ""
}

func (m *Params) GetHistoricalEntries() int64 {
	if m != nil {
		return m.HistoricalEntries
	}
	return 0
}

func (m *Params) GetUnbondingPeriod() time.Duration {
	if m != nil {
		return m.UnbondingPeriod
	}
	return 0
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

// MaturingVSCPacket contains the maturing time of a received VSCPacket
type MaturingVSCPacket struct {
	VscId        uint64    `protobuf:"varint,1,opt,name=vscId,proto3" json:"vscId,omitempty"`
	MaturityTime time.Time `protobuf:"bytes,2,opt,name=maturity_time,json=maturityTime,proto3,stdtime" json:"maturity_time"`
}

func (m *MaturingVSCPacket) Reset()         { *m = MaturingVSCPacket{} }
func (m *MaturingVSCPacket) String() string { return proto.CompactTextString(m) }
func (*MaturingVSCPacket) ProtoMessage()    {}
func (*MaturingVSCPacket) Descriptor() ([]byte, []int) {
	return fileDescriptor_5b27a82b276e7f93, []int{3}
}
func (m *MaturingVSCPacket) XXX_Unmarshal(b []byte) error {
	return m.Unmarshal(b)
}
func (m *MaturingVSCPacket) XXX_Marshal(b []byte, deterministic bool) ([]byte, error) {
	if deterministic {
		return xxx_messageInfo_MaturingVSCPacket.Marshal(b, m, deterministic)
	} else {
		b = b[:cap(b)]
		n, err := m.MarshalToSizedBuffer(b)
		if err != nil {
			return nil, err
		}
		return b[:n], nil
	}
}
func (m *MaturingVSCPacket) XXX_Merge(src proto.Message) {
	xxx_messageInfo_MaturingVSCPacket.Merge(m, src)
}
func (m *MaturingVSCPacket) XXX_Size() int {
	return m.Size()
}
func (m *MaturingVSCPacket) XXX_DiscardUnknown() {
	xxx_messageInfo_MaturingVSCPacket.DiscardUnknown(m)
}

var xxx_messageInfo_MaturingVSCPacket proto.InternalMessageInfo

func (m *MaturingVSCPacket) GetVscId() uint64 {
	if m != nil {
		return m.VscId
	}
	return 0
}

func (m *MaturingVSCPacket) GetMaturityTime() time.Time {
	if m != nil {
		return m.MaturityTime
	}
	return time.Time{}
}

func init() {
	proto.RegisterType((*Params)(nil), "interchain_security.ccv.consumer.v1.Params")
	proto.RegisterType((*LastTransmissionBlockHeight)(nil), "interchain_security.ccv.consumer.v1.LastTransmissionBlockHeight")
	proto.RegisterType((*CrossChainValidator)(nil), "interchain_security.ccv.consumer.v1.CrossChainValidator")
	proto.RegisterType((*MaturingVSCPacket)(nil), "interchain_security.ccv.consumer.v1.MaturingVSCPacket")
}

func init() {
	proto.RegisterFile("interchain_security/ccv/consumer/v1/consumer.proto", fileDescriptor_5b27a82b276e7f93)
}

var fileDescriptor_5b27a82b276e7f93 = []byte{
	// 709 bytes of a gzipped FileDescriptorProto
	0x1f, 0x8b, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, 0xff, 0x8c, 0x54, 0xcf, 0x4e, 0xdb, 0x48,
	0x18, 0x8f, 0x17, 0x08, 0x30, 0xb0, 0x5a, 0xf0, 0x66, 0xc1, 0x64, 0x25, 0x27, 0x64, 0x39, 0xe4,
	0x82, 0x23, 0x82, 0xf6, 0xc2, 0x8d, 0x84, 0x45, 0xb0, 0xfd, 0x97, 0x9a, 0x88, 0x43, 0x7b, 0xb0,
	0xc6, 0xe3, 0x89, 0x33, 0xc2, 0x9e, 0xb1, 0x66, 0xc6, 0x6e, 0xfd, 0x16, 0x1c, 0xfb, 0x08, 0x7d,
	0x80, 0x3e, 0x04, 0xea, 0x89, 0x63, 0x4f, 0xb4, 0x82, 0x37, 0xa8, 0xfa, 0x00, 0x95, 0x3d, 0x76,
	0x20, 0x50, 0x24, 0x6e, 0xdf, 0xa7, 0xdf, 0x1f, 0xcf, 0xf7, 0xf3, 0x37, 0x03, 0xba, 0x84, 0x4a,
	0xcc, 0xd1, 0x18, 0x12, 0xea, 0x08, 0x8c, 0x62, 0x4e, 0x64, 0xda, 0x41, 0x28, 0xe9, 0x20, 0x46,
	0x45, 0x1c, 0x62, 0xde, 0x49, 0x76, 0x26, 0xb5, 0x15, 0x71, 0x26, 0x99, 0xfe, 0xcf, 0x2f, 0x34,
	0x16, 0x42, 0x89, 0x35, 0xe1, 0x25, 0x3b, 0xf5, 0xad, 0xc7, 0x8c, 0x33, 0x3f, 0x94, 0x28, 0xab,
	0xfa, 0x86, 0xcf, 0x98, 0x1f, 0xe0, 0x4e, 0xde, 0xb9, 0xf1, 0xa8, 0x03, 0x69, 0x5a, 0x40, 0x35,
	0x9f, 0xf9, 0x2c, 0x2f, 0x3b, 0x59, 0x55, 0x0a, 0x10, 0x13, 0x21, 0x13, 0x8e, 0x02, 0x54, 0x53,
	0x40, 0xe6, 0x7d, 0x2f, 0x2f, 0xe6, 0x50, 0x12, 0x46, 0x0b, 0xbc, 0x71, 0x1f, 0x97, 0x24, 0xc4,
	0x42, 0xc2, 0x30, 0x52, 0x84, 0xd6, 0x8f, 0x59, 0x50, 0x1d, 0x40, 0x0e, 0x43, 0xa1, 0x1b, 0x60,
	0x1e, 0x53, 0xe8, 0x06, 0xd8, 0x33, 0xb4, 0xa6, 0xd6, 0x5e, 0xb0, 0xcb, 0x56, 0x7f, 0x05, 0xb6,
	0xdc, 0x80, 0xa1, 0x33, 0xe1, 0x44, 0x98, 0x3b, 0x1e, 0x11, 0x92, 0x13, 0x37, 0xce, 0x3e, 0xe3,
	0x48, 0x0e, 0xa9, 0x08, 0x89, 0x10, 0x84, 0x51, 0xe3, 0xb7, 0xa6, 0xd6, 0x9e, 0xb1, 0x37, 0x15,
	0x77, 0x80, 0xf9, 0xc1, 0x1d, 0xe6, 0xf0, 0x0e, 0x51, 0xff, 0x1f, 0x6c, 0x3e, 0xea, 0xe2, 0xa0,
	0x31, 0xa4, 0x14, 0x07, 0xc6, 0x4c, 0x53, 0x6b, 0x2f, 0xda, 0x0d, 0xef, 0x11, 0x93, 0xbe, 0xa2,
	0xe9, 0x7b, 0xa0, 0x1e, 0x71, 0x96, 0x10, 0x0f, 0x73, 0x67, 0x84, 0xb1, 0x13, 0x31, 0x16, 0x38,
	0xd0, 0xf3, 0xb8, 0x23, 0x24, 0x37, 0x66, 0x73, 0x93, 0xb5, 0x92, 0x71, 0x88, 0xf1, 0x80, 0xb1,
	0x60, 0xdf, 0xf3, 0xf8, 0x89, 0xe4, 0xfa, 0x6b, 0xa0, 0x23, 0x94, 0x38, 0x59, 0x28, 0x2c, 0x96,
	0xd9, 0x74, 0x84, 0x79, 0xc6, 0x5c, 0x53, 0x6b, 0x2f, 0x75, 0x37, 0x2c, 0x95, 0x9d, 0x55, 0x66,
	0x67, 0x1d, 0x14, 0xd9, 0xf6, 0x16, 0x2e, 0xae, 0x1a, 0x95, 0x0f, 0x5f, 0x1b, 0x9a, 0xbd, 0x82,
	0x50, 0x32, 0x54, 0xea, 0x41, 0x2e, 0xd6, 0xdf, 0x82, 0xf5, 0x7c, 0x9a, 0x11, 0xe6, 0xf7, 0x7d,
	0xab, 0x4f, 0xf7, 0xfd, 0xab, 0xf4, 0x98, 0x36, 0x3f, 0x02, 0xcd, 0x72, 0xdf, 0x1c, 0x8e, 0xa7,
	0x22, 0x1c, 0x71, 0x88, 0xb2, 0xc2, 0x98, 0xcf, 0x27, 0x36, 0x4b, 0x9e, 0x3d, 0x45, 0x3b, 0x2c,
	0x58, 0xfa, 0x36, 0xd0, 0xc7, 0x44, 0x48, 0xc6, 0x09, 0x82, 0x81, 0x83, 0xa9, 0xe4, 0x04, 0x0b,
	0x63, 0x21, 0xff, 0x81, 0xab, 0xb7, 0xc8, 0x7f, 0x0a, 0xd0, 0x5f, 0x82, 0x95, 0x98, 0xba, 0x8c,
	0x7a, 0x84, 0xfa, 0xe5, 0x38, 0x8b, 0x4f, 0x1f, 0xe7, 0x8f, 0x89, 0x58, 0x0d, 0xd2, 0xfa, 0x17,
	0xfc, 0xfd, 0x1c, 0x0a, 0x79, 0xf7, 0x7f, 0xf6, 0xb2, 0xad, 0x39, 0xc2, 0xc4, 0x1f, 0x4b, 0x7d,
	0x0d, 0x54, 0xc7, 0x79, 0x95, 0x6f, 0xe2, 0x8c, 0x5d, 0x74, 0xad, 0x8f, 0x1a, 0xf8, 0xb3, 0xcf,
	0x99, 0x10, 0xfd, 0xec, 0x8e, 0x9d, 0xc2, 0x80, 0x78, 0x50, 0x32, 0x9e, 0xad, 0x6e, 0xf6, 0xc7,
	0xb1, 0x10, 0xb9, 0x60, 0xd9, 0x2e, 0x5b, 0xbd, 0x06, 0xe6, 0x22, 0xf6, 0x0e, 0xf3, 0x62, 0x37,
	0x55, 0xa3, 0x43, 0x50, 0x8d, 0x62, 0xf7, 0x0c, 0xa7, 0xf9, 0x92, 0x2d, 0x75, 0x6b, 0x0f, 0x86,
	0xd8, 0xa7, 0x69, 0x6f, 0xf7, 0xfb, 0x55, 0x63, 0x3d, 0x85, 0x61, 0xb0, 0xd7, 0xca, 0xd2, 0xc4,
	0x54, 0xc4, 0xc2, 0x51, 0xba, 0xd6, 0xe7, 0x4f, 0xdb, 0xb5, 0xe2, 0x26, 0x22, 0x9e, 0x46, 0x92,
	0x59, 0x83, 0xd8, 0x7d, 0x86, 0x53, 0xbb, 0x30, 0x6e, 0x49, 0xb0, 0xfa, 0x02, 0xca, 0x98, 0x13,
	0xea, 0x9f, 0x9e, 0xf4, 0x07, 0x10, 0x9d, 0x61, 0x99, 0x9d, 0x26, 0x11, 0xe8, 0x58, 0x5d, 0xb0,
	0x59, 0x5b, 0x35, 0xfa, 0x31, 0xf8, 0x3d, 0xcc, 0xa9, 0x32, 0xcd, 0x57, 0x26, 0x3f, 0xeb, 0x52,
	0xb7, 0xfe, 0xe0, 0x50, 0xc3, 0xf2, 0xf2, 0xaa, 0x68, 0xcf, 0xb3, 0x68, 0x97, 0x4b, 0x69, 0x06,
	0xf6, 0x86, 0x17, 0xd7, 0xa6, 0x76, 0x79, 0x6d, 0x6a, 0xdf, 0xae, 0x4d, 0xed, 0xfc, 0xc6, 0xac,
	0x5c, 0xde, 0x98, 0x95, 0x2f, 0x37, 0x66, 0xe5, 0xcd, 0x9e, 0x4f, 0xe4, 0x38, 0x76, 0x2d, 0xc4,
	0xc2, 0xe2, 0x09, 0xe9, 0xdc, 0xbe, 0x56, 0xdb, 0x93, 0xd7, 0xea, 0xfd, 0xf4, 0x43, 0x28, 0xd3,
	0x08, 0x0b, 0xb7, 0x9a, 0x9f, 0x60, 0xf7, 0x67, 0x00, 0x00, 0x00, 0xff, 0xff, 0xde, 0xaf, 0xcf,
	0x76, 0x39, 0x05, 0x00, 0x00,
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
	n1, err1 := github_com_gogo_protobuf_types.StdDurationMarshalTo(m.UnbondingPeriod, dAtA[i-github_com_gogo_protobuf_types.SizeOfStdDuration(m.UnbondingPeriod):])
	if err1 != nil {
		return 0, err1
	}
	i -= n1
	i = encodeVarintConsumer(dAtA, i, uint64(n1))
	i--
	dAtA[i] = 0x4a
	if m.HistoricalEntries != 0 {
		i = encodeVarintConsumer(dAtA, i, uint64(m.HistoricalEntries))
		i--
		dAtA[i] = 0x40
	}
	if len(m.ConsumerRedistributionFraction) > 0 {
		i -= len(m.ConsumerRedistributionFraction)
		copy(dAtA[i:], m.ConsumerRedistributionFraction)
		i = encodeVarintConsumer(dAtA, i, uint64(len(m.ConsumerRedistributionFraction)))
		i--
		dAtA[i] = 0x3a
	}
	n2, err2 := github_com_gogo_protobuf_types.StdDurationMarshalTo(m.TransferTimeoutPeriod, dAtA[i-github_com_gogo_protobuf_types.SizeOfStdDuration(m.TransferTimeoutPeriod):])
	if err2 != nil {
		return 0, err2
	}
	i -= n2
	i = encodeVarintConsumer(dAtA, i, uint64(n2))
	i--
	dAtA[i] = 0x32
	n3, err3 := github_com_gogo_protobuf_types.StdDurationMarshalTo(m.CcvTimeoutPeriod, dAtA[i-github_com_gogo_protobuf_types.SizeOfStdDuration(m.CcvTimeoutPeriod):])
	if err3 != nil {
		return 0, err3
	}
	i -= n3
	i = encodeVarintConsumer(dAtA, i, uint64(n3))
	i--
	dAtA[i] = 0x2a
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

func (m *MaturingVSCPacket) Marshal() (dAtA []byte, err error) {
	size := m.Size()
	dAtA = make([]byte, size)
	n, err := m.MarshalToSizedBuffer(dAtA[:size])
	if err != nil {
		return nil, err
	}
	return dAtA[:n], nil
}

func (m *MaturingVSCPacket) MarshalTo(dAtA []byte) (int, error) {
	size := m.Size()
	return m.MarshalToSizedBuffer(dAtA[:size])
}

func (m *MaturingVSCPacket) MarshalToSizedBuffer(dAtA []byte) (int, error) {
	i := len(dAtA)
	_ = i
	var l int
	_ = l
	n5, err5 := github_com_gogo_protobuf_types.StdTimeMarshalTo(m.MaturityTime, dAtA[i-github_com_gogo_protobuf_types.SizeOfStdTime(m.MaturityTime):])
	if err5 != nil {
		return 0, err5
	}
	i -= n5
	i = encodeVarintConsumer(dAtA, i, uint64(n5))
	i--
	dAtA[i] = 0x12
	if m.VscId != 0 {
		i = encodeVarintConsumer(dAtA, i, uint64(m.VscId))
		i--
		dAtA[i] = 0x8
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
	l = github_com_gogo_protobuf_types.SizeOfStdDuration(m.CcvTimeoutPeriod)
	n += 1 + l + sovConsumer(uint64(l))
	l = github_com_gogo_protobuf_types.SizeOfStdDuration(m.TransferTimeoutPeriod)
	n += 1 + l + sovConsumer(uint64(l))
	l = len(m.ConsumerRedistributionFraction)
	if l > 0 {
		n += 1 + l + sovConsumer(uint64(l))
	}
	if m.HistoricalEntries != 0 {
		n += 1 + sovConsumer(uint64(m.HistoricalEntries))
	}
	l = github_com_gogo_protobuf_types.SizeOfStdDuration(m.UnbondingPeriod)
	n += 1 + l + sovConsumer(uint64(l))
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

func (m *MaturingVSCPacket) Size() (n int) {
	if m == nil {
		return 0
	}
	var l int
	_ = l
	if m.VscId != 0 {
		n += 1 + sovConsumer(uint64(m.VscId))
	}
	l = github_com_gogo_protobuf_types.SizeOfStdTime(m.MaturityTime)
	n += 1 + l + sovConsumer(uint64(l))
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
				return fmt.Errorf("proto: wrong wireType = %d for field CcvTimeoutPeriod", wireType)
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
			if err := github_com_gogo_protobuf_types.StdDurationUnmarshal(&m.CcvTimeoutPeriod, dAtA[iNdEx:postIndex]); err != nil {
				return err
			}
			iNdEx = postIndex
		case 6:
			if wireType != 2 {
				return fmt.Errorf("proto: wrong wireType = %d for field TransferTimeoutPeriod", wireType)
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
			if err := github_com_gogo_protobuf_types.StdDurationUnmarshal(&m.TransferTimeoutPeriod, dAtA[iNdEx:postIndex]); err != nil {
				return err
			}
			iNdEx = postIndex
		case 7:
			if wireType != 2 {
				return fmt.Errorf("proto: wrong wireType = %d for field ConsumerRedistributionFraction", wireType)
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
			m.ConsumerRedistributionFraction = string(dAtA[iNdEx:postIndex])
			iNdEx = postIndex
		case 8:
			if wireType != 0 {
				return fmt.Errorf("proto: wrong wireType = %d for field HistoricalEntries", wireType)
			}
			m.HistoricalEntries = 0
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowConsumer
				}
				if iNdEx >= l {
					return io.ErrUnexpectedEOF
				}
				b := dAtA[iNdEx]
				iNdEx++
				m.HistoricalEntries |= int64(b&0x7F) << shift
				if b < 0x80 {
					break
				}
			}
		case 9:
			if wireType != 2 {
				return fmt.Errorf("proto: wrong wireType = %d for field UnbondingPeriod", wireType)
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
			if err := github_com_gogo_protobuf_types.StdDurationUnmarshal(&m.UnbondingPeriod, dAtA[iNdEx:postIndex]); err != nil {
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
func (m *MaturingVSCPacket) Unmarshal(dAtA []byte) error {
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
			return fmt.Errorf("proto: MaturingVSCPacket: wiretype end group for non-group")
		}
		if fieldNum <= 0 {
			return fmt.Errorf("proto: MaturingVSCPacket: illegal tag %d (wire type %d)", fieldNum, wire)
		}
		switch fieldNum {
		case 1:
			if wireType != 0 {
				return fmt.Errorf("proto: wrong wireType = %d for field VscId", wireType)
			}
			m.VscId = 0
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowConsumer
				}
				if iNdEx >= l {
					return io.ErrUnexpectedEOF
				}
				b := dAtA[iNdEx]
				iNdEx++
				m.VscId |= uint64(b&0x7F) << shift
				if b < 0x80 {
					break
				}
			}
		case 2:
			if wireType != 2 {
				return fmt.Errorf("proto: wrong wireType = %d for field MaturityTime", wireType)
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
			if err := github_com_gogo_protobuf_types.StdTimeUnmarshal(&m.MaturityTime, dAtA[iNdEx:postIndex]); err != nil {
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
