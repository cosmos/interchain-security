// Code generated by protoc-gen-gogo. DO NOT EDIT.
// source: interchain_security/ccv/v1/ccv.proto

package types

import (
	fmt "fmt"
	types1 "github.com/cosmos/cosmos-sdk/x/staking/types"
	_ "github.com/gogo/protobuf/gogoproto"
	proto "github.com/gogo/protobuf/proto"
	types "github.com/tendermint/tendermint/abci/types"
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

// This packet is sent from provider chain to consumer chain if the validator
// set for consumer chain changes (due to new bonding/unbonding messages or
// slashing events) A VSCMatured packet from consumer chain will be sent
// asynchronously once unbonding period is over, and this will function as
// `UnbondingOver` message for this packet.
type ValidatorSetChangePacketData struct {
	ValidatorUpdates []types.ValidatorUpdate `protobuf:"bytes,1,rep,name=validator_updates,json=validatorUpdates,proto3" json:"validator_updates" yaml:"validator_updates"`
	ValsetUpdateId   uint64                  `protobuf:"varint,2,opt,name=valset_update_id,json=valsetUpdateId,proto3" json:"valset_update_id,omitempty"`
	// consensus address of consumer chain validators
	// successfully slashed on the provider chain
	SlashAcks []string `protobuf:"bytes,3,rep,name=slash_acks,json=slashAcks,proto3" json:"slash_acks,omitempty"`
}

func (m *ValidatorSetChangePacketData) Reset()         { *m = ValidatorSetChangePacketData{} }
func (m *ValidatorSetChangePacketData) String() string { return proto.CompactTextString(m) }
func (*ValidatorSetChangePacketData) ProtoMessage()    {}
func (*ValidatorSetChangePacketData) Descriptor() ([]byte, []int) {
	return fileDescriptor_68bd5f3242e6f29c, []int{0}
}
func (m *ValidatorSetChangePacketData) XXX_Unmarshal(b []byte) error {
	return m.Unmarshal(b)
}
func (m *ValidatorSetChangePacketData) XXX_Marshal(b []byte, deterministic bool) ([]byte, error) {
	if deterministic {
		return xxx_messageInfo_ValidatorSetChangePacketData.Marshal(b, m, deterministic)
	} else {
		b = b[:cap(b)]
		n, err := m.MarshalToSizedBuffer(b)
		if err != nil {
			return nil, err
		}
		return b[:n], nil
	}
}
func (m *ValidatorSetChangePacketData) XXX_Merge(src proto.Message) {
	xxx_messageInfo_ValidatorSetChangePacketData.Merge(m, src)
}
func (m *ValidatorSetChangePacketData) XXX_Size() int {
	return m.Size()
}
func (m *ValidatorSetChangePacketData) XXX_DiscardUnknown() {
	xxx_messageInfo_ValidatorSetChangePacketData.DiscardUnknown(m)
}

var xxx_messageInfo_ValidatorSetChangePacketData proto.InternalMessageInfo

func (m *ValidatorSetChangePacketData) GetValidatorUpdates() []types.ValidatorUpdate {
	if m != nil {
		return m.ValidatorUpdates
	}
	return nil
}

func (m *ValidatorSetChangePacketData) GetValsetUpdateId() uint64 {
	if m != nil {
		return m.ValsetUpdateId
	}
	return 0
}

func (m *ValidatorSetChangePacketData) GetSlashAcks() []string {
	if m != nil {
		return m.SlashAcks
	}
	return nil
}

type UnbondingOp struct {
	Id uint64 `protobuf:"varint,1,opt,name=id,proto3" json:"id,omitempty"`
	// consumer chains that are still unbonding
	UnbondingConsumerChains []string `protobuf:"bytes,2,rep,name=unbonding_consumer_chains,json=unbondingConsumerChains,proto3" json:"unbonding_consumer_chains,omitempty"`
}

func (m *UnbondingOp) Reset()         { *m = UnbondingOp{} }
func (m *UnbondingOp) String() string { return proto.CompactTextString(m) }
func (*UnbondingOp) ProtoMessage()    {}
func (*UnbondingOp) Descriptor() ([]byte, []int) {
	return fileDescriptor_68bd5f3242e6f29c, []int{1}
}
func (m *UnbondingOp) XXX_Unmarshal(b []byte) error {
	return m.Unmarshal(b)
}
func (m *UnbondingOp) XXX_Marshal(b []byte, deterministic bool) ([]byte, error) {
	if deterministic {
		return xxx_messageInfo_UnbondingOp.Marshal(b, m, deterministic)
	} else {
		b = b[:cap(b)]
		n, err := m.MarshalToSizedBuffer(b)
		if err != nil {
			return nil, err
		}
		return b[:n], nil
	}
}
func (m *UnbondingOp) XXX_Merge(src proto.Message) {
	xxx_messageInfo_UnbondingOp.Merge(m, src)
}
func (m *UnbondingOp) XXX_Size() int {
	return m.Size()
}
func (m *UnbondingOp) XXX_DiscardUnknown() {
	xxx_messageInfo_UnbondingOp.DiscardUnknown(m)
}

var xxx_messageInfo_UnbondingOp proto.InternalMessageInfo

func (m *UnbondingOp) GetId() uint64 {
	if m != nil {
		return m.Id
	}
	return 0
}

func (m *UnbondingOp) GetUnbondingConsumerChains() []string {
	if m != nil {
		return m.UnbondingConsumerChains
	}
	return nil
}

// This packet is sent from the consumer chain to the provider chain
// to notify that a VSC packet reached maturity on the consumer chain.
type VSCMaturedPacketData struct {
	// the id of the VSC packet that reached maturity
	ValsetUpdateId uint64 `protobuf:"varint,1,opt,name=valset_update_id,json=valsetUpdateId,proto3" json:"valset_update_id,omitempty"`
}

func (m *VSCMaturedPacketData) Reset()         { *m = VSCMaturedPacketData{} }
func (m *VSCMaturedPacketData) String() string { return proto.CompactTextString(m) }
func (*VSCMaturedPacketData) ProtoMessage()    {}
func (*VSCMaturedPacketData) Descriptor() ([]byte, []int) {
	return fileDescriptor_68bd5f3242e6f29c, []int{2}
}
func (m *VSCMaturedPacketData) XXX_Unmarshal(b []byte) error {
	return m.Unmarshal(b)
}
func (m *VSCMaturedPacketData) XXX_Marshal(b []byte, deterministic bool) ([]byte, error) {
	if deterministic {
		return xxx_messageInfo_VSCMaturedPacketData.Marshal(b, m, deterministic)
	} else {
		b = b[:cap(b)]
		n, err := m.MarshalToSizedBuffer(b)
		if err != nil {
			return nil, err
		}
		return b[:n], nil
	}
}
func (m *VSCMaturedPacketData) XXX_Merge(src proto.Message) {
	xxx_messageInfo_VSCMaturedPacketData.Merge(m, src)
}
func (m *VSCMaturedPacketData) XXX_Size() int {
	return m.Size()
}
func (m *VSCMaturedPacketData) XXX_DiscardUnknown() {
	xxx_messageInfo_VSCMaturedPacketData.DiscardUnknown(m)
}

var xxx_messageInfo_VSCMaturedPacketData proto.InternalMessageInfo

func (m *VSCMaturedPacketData) GetValsetUpdateId() uint64 {
	if m != nil {
		return m.ValsetUpdateId
	}
	return 0
}

// This packet is sent from the consumer chain to the provider chain
// to request the slashing of a validator as a result of an infraction
// committed on the consumer chain.
type SlashPacketData struct {
	Validator types.Validator `protobuf:"bytes,1,opt,name=validator,proto3" json:"validator" yaml:"validator"`
	// map to the infraction block height on the provider
	ValsetUpdateId uint64 `protobuf:"varint,2,opt,name=valset_update_id,json=valsetUpdateId,proto3" json:"valset_update_id,omitempty"`
	// tell if the slashing is for a downtime or a double-signing infraction
	Infraction types1.InfractionType `protobuf:"varint,3,opt,name=infraction,proto3,enum=cosmos.staking.v1beta1.InfractionType" json:"infraction,omitempty"`
}

func (m *SlashPacketData) Reset()         { *m = SlashPacketData{} }
func (m *SlashPacketData) String() string { return proto.CompactTextString(m) }
func (*SlashPacketData) ProtoMessage()    {}
func (*SlashPacketData) Descriptor() ([]byte, []int) {
	return fileDescriptor_68bd5f3242e6f29c, []int{3}
}
func (m *SlashPacketData) XXX_Unmarshal(b []byte) error {
	return m.Unmarshal(b)
}
func (m *SlashPacketData) XXX_Marshal(b []byte, deterministic bool) ([]byte, error) {
	if deterministic {
		return xxx_messageInfo_SlashPacketData.Marshal(b, m, deterministic)
	} else {
		b = b[:cap(b)]
		n, err := m.MarshalToSizedBuffer(b)
		if err != nil {
			return nil, err
		}
		return b[:n], nil
	}
}
func (m *SlashPacketData) XXX_Merge(src proto.Message) {
	xxx_messageInfo_SlashPacketData.Merge(m, src)
}
func (m *SlashPacketData) XXX_Size() int {
	return m.Size()
}
func (m *SlashPacketData) XXX_DiscardUnknown() {
	xxx_messageInfo_SlashPacketData.DiscardUnknown(m)
}

var xxx_messageInfo_SlashPacketData proto.InternalMessageInfo

func (m *SlashPacketData) GetValidator() types.Validator {
	if m != nil {
		return m.Validator
	}
	return types.Validator{}
}

func (m *SlashPacketData) GetValsetUpdateId() uint64 {
	if m != nil {
		return m.ValsetUpdateId
	}
	return 0
}

func (m *SlashPacketData) GetInfraction() types1.InfractionType {
	if m != nil {
		return m.Infraction
	}
	return types1.InfractionEmpty
}

// UnbondingOpsIndex defines a list of unbonding operation ids.
type UnbondingOpsIndex struct {
	Ids []uint64 `protobuf:"varint,1,rep,packed,name=ids,proto3" json:"ids,omitempty"`
}

func (m *UnbondingOpsIndex) Reset()         { *m = UnbondingOpsIndex{} }
func (m *UnbondingOpsIndex) String() string { return proto.CompactTextString(m) }
func (*UnbondingOpsIndex) ProtoMessage()    {}
func (*UnbondingOpsIndex) Descriptor() ([]byte, []int) {
	return fileDescriptor_68bd5f3242e6f29c, []int{4}
}
func (m *UnbondingOpsIndex) XXX_Unmarshal(b []byte) error {
	return m.Unmarshal(b)
}
func (m *UnbondingOpsIndex) XXX_Marshal(b []byte, deterministic bool) ([]byte, error) {
	if deterministic {
		return xxx_messageInfo_UnbondingOpsIndex.Marshal(b, m, deterministic)
	} else {
		b = b[:cap(b)]
		n, err := m.MarshalToSizedBuffer(b)
		if err != nil {
			return nil, err
		}
		return b[:n], nil
	}
}
func (m *UnbondingOpsIndex) XXX_Merge(src proto.Message) {
	xxx_messageInfo_UnbondingOpsIndex.Merge(m, src)
}
func (m *UnbondingOpsIndex) XXX_Size() int {
	return m.Size()
}
func (m *UnbondingOpsIndex) XXX_DiscardUnknown() {
	xxx_messageInfo_UnbondingOpsIndex.DiscardUnknown(m)
}

var xxx_messageInfo_UnbondingOpsIndex proto.InternalMessageInfo

func (m *UnbondingOpsIndex) GetIds() []uint64 {
	if m != nil {
		return m.Ids
	}
	return nil
}

// MaturedUnbondingOps defines a list of ids corresponding to ids of matured
// unbonding operations.
type MaturedUnbondingOps struct {
	Ids []uint64 `protobuf:"varint,1,rep,packed,name=ids,proto3" json:"ids,omitempty"`
}

func (m *MaturedUnbondingOps) Reset()         { *m = MaturedUnbondingOps{} }
func (m *MaturedUnbondingOps) String() string { return proto.CompactTextString(m) }
func (*MaturedUnbondingOps) ProtoMessage()    {}
func (*MaturedUnbondingOps) Descriptor() ([]byte, []int) {
	return fileDescriptor_68bd5f3242e6f29c, []int{5}
}
func (m *MaturedUnbondingOps) XXX_Unmarshal(b []byte) error {
	return m.Unmarshal(b)
}
func (m *MaturedUnbondingOps) XXX_Marshal(b []byte, deterministic bool) ([]byte, error) {
	if deterministic {
		return xxx_messageInfo_MaturedUnbondingOps.Marshal(b, m, deterministic)
	} else {
		b = b[:cap(b)]
		n, err := m.MarshalToSizedBuffer(b)
		if err != nil {
			return nil, err
		}
		return b[:n], nil
	}
}
func (m *MaturedUnbondingOps) XXX_Merge(src proto.Message) {
	xxx_messageInfo_MaturedUnbondingOps.Merge(m, src)
}
func (m *MaturedUnbondingOps) XXX_Size() int {
	return m.Size()
}
func (m *MaturedUnbondingOps) XXX_DiscardUnknown() {
	xxx_messageInfo_MaturedUnbondingOps.DiscardUnknown(m)
}

var xxx_messageInfo_MaturedUnbondingOps proto.InternalMessageInfo

func (m *MaturedUnbondingOps) GetIds() []uint64 {
	if m != nil {
		return m.Ids
	}
	return nil
}

func init() {
	proto.RegisterType((*ValidatorSetChangePacketData)(nil), "interchain_security.ccv.v1.ValidatorSetChangePacketData")
	proto.RegisterType((*UnbondingOp)(nil), "interchain_security.ccv.v1.UnbondingOp")
	proto.RegisterType((*VSCMaturedPacketData)(nil), "interchain_security.ccv.v1.VSCMaturedPacketData")
	proto.RegisterType((*SlashPacketData)(nil), "interchain_security.ccv.v1.SlashPacketData")
	proto.RegisterType((*UnbondingOpsIndex)(nil), "interchain_security.ccv.v1.UnbondingOpsIndex")
	proto.RegisterType((*MaturedUnbondingOps)(nil), "interchain_security.ccv.v1.MaturedUnbondingOps")
}

func init() {
	proto.RegisterFile("interchain_security/ccv/v1/ccv.proto", fileDescriptor_68bd5f3242e6f29c)
}

var fileDescriptor_68bd5f3242e6f29c = []byte{
	// 509 bytes of a gzipped FileDescriptorProto
	0x1f, 0x8b, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, 0xff, 0x94, 0x53, 0x41, 0x8b, 0xd3, 0x40,
	0x14, 0xee, 0xb4, 0x8b, 0xb0, 0x53, 0xa8, 0xdd, 0xb8, 0x60, 0xac, 0x9a, 0x0d, 0x61, 0xd5, 0x5e,
	0x4c, 0x68, 0xbd, 0xed, 0x49, 0x5b, 0x11, 0x8a, 0x88, 0x92, 0xba, 0x0b, 0x7a, 0x09, 0xd3, 0x99,
	0x31, 0x1d, 0xda, 0xcc, 0x84, 0xcc, 0x24, 0x6c, 0xff, 0x85, 0x3f, 0x6b, 0x8f, 0x7b, 0x73, 0x4f,
	0x8b, 0xb4, 0xff, 0xc0, 0x5f, 0x20, 0x99, 0xa4, 0x69, 0x74, 0xeb, 0xc1, 0xd3, 0xbc, 0x79, 0xdf,
	0xf7, 0x3e, 0x1e, 0x1f, 0xdf, 0x83, 0xa7, 0x8c, 0x2b, 0x9a, 0xe0, 0x39, 0x62, 0x3c, 0x90, 0x14,
	0xa7, 0x09, 0x53, 0x2b, 0x0f, 0xe3, 0xcc, 0xcb, 0x06, 0xf9, 0xe3, 0xc6, 0x89, 0x50, 0xc2, 0xe8,
	0xed, 0x61, 0xb9, 0x39, 0x9c, 0x0d, 0x7a, 0xa7, 0x58, 0xc8, 0x48, 0x48, 0x4f, 0x2a, 0xb4, 0x60,
	0x3c, 0xf4, 0xb2, 0xc1, 0x8c, 0x2a, 0x34, 0xd8, 0xfe, 0x0b, 0x85, 0xde, 0x71, 0x28, 0x42, 0xa1,
	0x4b, 0x2f, 0xaf, 0xca, 0xee, 0x63, 0x45, 0x39, 0xa1, 0x49, 0xc4, 0xb8, 0xf2, 0xd0, 0x0c, 0x33,
	0x4f, 0xad, 0x62, 0x2a, 0x0b, 0xd0, 0xb9, 0x01, 0xf0, 0xc9, 0x05, 0x5a, 0x32, 0x82, 0x94, 0x48,
	0xa6, 0x54, 0x8d, 0xe7, 0x88, 0x87, 0xf4, 0x13, 0xc2, 0x0b, 0xaa, 0xde, 0x22, 0x85, 0x0c, 0x01,
	0x8f, 0xb2, 0x2d, 0x1e, 0xa4, 0x31, 0x41, 0x8a, 0x4a, 0x13, 0xd8, 0xad, 0x7e, 0x7b, 0x68, 0xbb,
	0x3b, 0x65, 0x37, 0x57, 0x76, 0x2b, 0xa5, 0x73, 0x4d, 0x1c, 0xd9, 0x57, 0xb7, 0x27, 0x8d, 0x5f,
	0xb7, 0x27, 0xe6, 0x0a, 0x45, 0xcb, 0x33, 0xe7, 0x8e, 0x90, 0xe3, 0x77, 0xb3, 0x3f, 0x47, 0xa4,
	0xd1, 0x87, 0x79, 0x4f, 0x52, 0x55, 0x92, 0x02, 0x46, 0xcc, 0xa6, 0x0d, 0xfa, 0x07, 0x7e, 0xa7,
	0xe8, 0x17, 0xc4, 0x09, 0x31, 0x9e, 0x42, 0x28, 0x97, 0x48, 0xce, 0x03, 0x84, 0x17, 0xd2, 0x6c,
	0xd9, 0xad, 0xfe, 0xa1, 0x7f, 0xa8, 0x3b, 0x6f, 0xf0, 0x42, 0x3a, 0x5f, 0x60, 0xfb, 0x9c, 0xcf,
	0x04, 0x27, 0x8c, 0x87, 0x1f, 0x63, 0xa3, 0x03, 0x9b, 0x8c, 0x98, 0x40, 0x2b, 0x35, 0x19, 0x31,
	0xce, 0xe0, 0xa3, 0x74, 0x0b, 0x07, 0x58, 0x70, 0x99, 0x46, 0x34, 0x09, 0xb4, 0xfd, 0xd2, 0x6c,
	0x6a, 0xb1, 0x87, 0x15, 0x61, 0x5c, 0xe2, 0x63, 0x0d, 0x3b, 0xaf, 0xe1, 0xf1, 0xc5, 0x74, 0xfc,
	0x01, 0xa9, 0x34, 0xa1, 0xa4, 0x66, 0xd6, 0xbe, 0xdd, 0xc1, 0xbe, 0xdd, 0x9d, 0x1f, 0x00, 0xde,
	0x9f, 0xe6, 0xab, 0xd6, 0xa6, 0x7d, 0x78, 0x58, 0xb9, 0xa1, 0xc7, 0xda, 0xc3, 0xde, 0xbf, 0x2d,
	0x1e, 0x99, 0xa5, 0xb9, 0xdd, 0xbf, 0xcc, 0x75, 0xfc, 0x9d, 0xcc, 0x7f, 0xb8, 0xf9, 0x0e, 0x42,
	0xc6, 0xbf, 0x25, 0x08, 0x2b, 0x26, 0xb8, 0xd9, 0xb2, 0x41, 0xbf, 0x33, 0x7c, 0xee, 0x16, 0xb9,
	0x73, 0xb7, 0x39, 0x2b, 0x73, 0xe7, 0x4e, 0x2a, 0xe6, 0xe7, 0x55, 0x4c, 0xfd, 0xda, 0xa4, 0xf3,
	0x0c, 0x1e, 0xd5, 0x6c, 0x97, 0x13, 0x4e, 0xe8, 0xa5, 0xd1, 0x85, 0x2d, 0x46, 0x8a, 0xdc, 0x1c,
	0xf8, 0x79, 0xe9, 0xbc, 0x80, 0x0f, 0x4a, 0xff, 0xea, 0xec, 0xbb, 0xc4, 0xd1, 0xfb, 0xab, 0xb5,
	0x05, 0xae, 0xd7, 0x16, 0xf8, 0xb9, 0xb6, 0xc0, 0xf7, 0x8d, 0xd5, 0xb8, 0xde, 0x58, 0x8d, 0x9b,
	0x8d, 0xd5, 0xf8, 0x3a, 0x08, 0x99, 0x9a, 0xa7, 0x33, 0x17, 0x8b, 0xc8, 0x2b, 0xef, 0x63, 0x77,
	0x42, 0x2f, 0xab, 0x43, 0xbb, 0xd4, 0xa7, 0xa6, 0x43, 0x3f, 0xbb, 0xa7, 0x53, 0xff, 0xea, 0x77,
	0x00, 0x00, 0x00, 0xff, 0xff, 0xf7, 0xaa, 0xb0, 0x21, 0x92, 0x03, 0x00, 0x00,
}

func (m *ValidatorSetChangePacketData) Marshal() (dAtA []byte, err error) {
	size := m.Size()
	dAtA = make([]byte, size)
	n, err := m.MarshalToSizedBuffer(dAtA[:size])
	if err != nil {
		return nil, err
	}
	return dAtA[:n], nil
}

func (m *ValidatorSetChangePacketData) MarshalTo(dAtA []byte) (int, error) {
	size := m.Size()
	return m.MarshalToSizedBuffer(dAtA[:size])
}

func (m *ValidatorSetChangePacketData) MarshalToSizedBuffer(dAtA []byte) (int, error) {
	i := len(dAtA)
	_ = i
	var l int
	_ = l
	if len(m.SlashAcks) > 0 {
		for iNdEx := len(m.SlashAcks) - 1; iNdEx >= 0; iNdEx-- {
			i -= len(m.SlashAcks[iNdEx])
			copy(dAtA[i:], m.SlashAcks[iNdEx])
			i = encodeVarintCcv(dAtA, i, uint64(len(m.SlashAcks[iNdEx])))
			i--
			dAtA[i] = 0x1a
		}
	}
	if m.ValsetUpdateId != 0 {
		i = encodeVarintCcv(dAtA, i, uint64(m.ValsetUpdateId))
		i--
		dAtA[i] = 0x10
	}
	if len(m.ValidatorUpdates) > 0 {
		for iNdEx := len(m.ValidatorUpdates) - 1; iNdEx >= 0; iNdEx-- {
			{
				size, err := m.ValidatorUpdates[iNdEx].MarshalToSizedBuffer(dAtA[:i])
				if err != nil {
					return 0, err
				}
				i -= size
				i = encodeVarintCcv(dAtA, i, uint64(size))
			}
			i--
			dAtA[i] = 0xa
		}
	}
	return len(dAtA) - i, nil
}

func (m *UnbondingOp) Marshal() (dAtA []byte, err error) {
	size := m.Size()
	dAtA = make([]byte, size)
	n, err := m.MarshalToSizedBuffer(dAtA[:size])
	if err != nil {
		return nil, err
	}
	return dAtA[:n], nil
}

func (m *UnbondingOp) MarshalTo(dAtA []byte) (int, error) {
	size := m.Size()
	return m.MarshalToSizedBuffer(dAtA[:size])
}

func (m *UnbondingOp) MarshalToSizedBuffer(dAtA []byte) (int, error) {
	i := len(dAtA)
	_ = i
	var l int
	_ = l
	if len(m.UnbondingConsumerChains) > 0 {
		for iNdEx := len(m.UnbondingConsumerChains) - 1; iNdEx >= 0; iNdEx-- {
			i -= len(m.UnbondingConsumerChains[iNdEx])
			copy(dAtA[i:], m.UnbondingConsumerChains[iNdEx])
			i = encodeVarintCcv(dAtA, i, uint64(len(m.UnbondingConsumerChains[iNdEx])))
			i--
			dAtA[i] = 0x12
		}
	}
	if m.Id != 0 {
		i = encodeVarintCcv(dAtA, i, uint64(m.Id))
		i--
		dAtA[i] = 0x8
	}
	return len(dAtA) - i, nil
}

func (m *VSCMaturedPacketData) Marshal() (dAtA []byte, err error) {
	size := m.Size()
	dAtA = make([]byte, size)
	n, err := m.MarshalToSizedBuffer(dAtA[:size])
	if err != nil {
		return nil, err
	}
	return dAtA[:n], nil
}

func (m *VSCMaturedPacketData) MarshalTo(dAtA []byte) (int, error) {
	size := m.Size()
	return m.MarshalToSizedBuffer(dAtA[:size])
}

func (m *VSCMaturedPacketData) MarshalToSizedBuffer(dAtA []byte) (int, error) {
	i := len(dAtA)
	_ = i
	var l int
	_ = l
	if m.ValsetUpdateId != 0 {
		i = encodeVarintCcv(dAtA, i, uint64(m.ValsetUpdateId))
		i--
		dAtA[i] = 0x8
	}
	return len(dAtA) - i, nil
}

func (m *SlashPacketData) Marshal() (dAtA []byte, err error) {
	size := m.Size()
	dAtA = make([]byte, size)
	n, err := m.MarshalToSizedBuffer(dAtA[:size])
	if err != nil {
		return nil, err
	}
	return dAtA[:n], nil
}

func (m *SlashPacketData) MarshalTo(dAtA []byte) (int, error) {
	size := m.Size()
	return m.MarshalToSizedBuffer(dAtA[:size])
}

func (m *SlashPacketData) MarshalToSizedBuffer(dAtA []byte) (int, error) {
	i := len(dAtA)
	_ = i
	var l int
	_ = l
	if m.Infraction != 0 {
		i = encodeVarintCcv(dAtA, i, uint64(m.Infraction))
		i--
		dAtA[i] = 0x18
	}
	if m.ValsetUpdateId != 0 {
		i = encodeVarintCcv(dAtA, i, uint64(m.ValsetUpdateId))
		i--
		dAtA[i] = 0x10
	}
	{
		size, err := m.Validator.MarshalToSizedBuffer(dAtA[:i])
		if err != nil {
			return 0, err
		}
		i -= size
		i = encodeVarintCcv(dAtA, i, uint64(size))
	}
	i--
	dAtA[i] = 0xa
	return len(dAtA) - i, nil
}

func (m *UnbondingOpsIndex) Marshal() (dAtA []byte, err error) {
	size := m.Size()
	dAtA = make([]byte, size)
	n, err := m.MarshalToSizedBuffer(dAtA[:size])
	if err != nil {
		return nil, err
	}
	return dAtA[:n], nil
}

func (m *UnbondingOpsIndex) MarshalTo(dAtA []byte) (int, error) {
	size := m.Size()
	return m.MarshalToSizedBuffer(dAtA[:size])
}

func (m *UnbondingOpsIndex) MarshalToSizedBuffer(dAtA []byte) (int, error) {
	i := len(dAtA)
	_ = i
	var l int
	_ = l
	if len(m.Ids) > 0 {
		dAtA3 := make([]byte, len(m.Ids)*10)
		var j2 int
		for _, num := range m.Ids {
			for num >= 1<<7 {
				dAtA3[j2] = uint8(uint64(num)&0x7f | 0x80)
				num >>= 7
				j2++
			}
			dAtA3[j2] = uint8(num)
			j2++
		}
		i -= j2
		copy(dAtA[i:], dAtA3[:j2])
		i = encodeVarintCcv(dAtA, i, uint64(j2))
		i--
		dAtA[i] = 0xa
	}
	return len(dAtA) - i, nil
}

func (m *MaturedUnbondingOps) Marshal() (dAtA []byte, err error) {
	size := m.Size()
	dAtA = make([]byte, size)
	n, err := m.MarshalToSizedBuffer(dAtA[:size])
	if err != nil {
		return nil, err
	}
	return dAtA[:n], nil
}

func (m *MaturedUnbondingOps) MarshalTo(dAtA []byte) (int, error) {
	size := m.Size()
	return m.MarshalToSizedBuffer(dAtA[:size])
}

func (m *MaturedUnbondingOps) MarshalToSizedBuffer(dAtA []byte) (int, error) {
	i := len(dAtA)
	_ = i
	var l int
	_ = l
	if len(m.Ids) > 0 {
		dAtA5 := make([]byte, len(m.Ids)*10)
		var j4 int
		for _, num := range m.Ids {
			for num >= 1<<7 {
				dAtA5[j4] = uint8(uint64(num)&0x7f | 0x80)
				num >>= 7
				j4++
			}
			dAtA5[j4] = uint8(num)
			j4++
		}
		i -= j4
		copy(dAtA[i:], dAtA5[:j4])
		i = encodeVarintCcv(dAtA, i, uint64(j4))
		i--
		dAtA[i] = 0xa
	}
	return len(dAtA) - i, nil
}

func encodeVarintCcv(dAtA []byte, offset int, v uint64) int {
	offset -= sovCcv(v)
	base := offset
	for v >= 1<<7 {
		dAtA[offset] = uint8(v&0x7f | 0x80)
		v >>= 7
		offset++
	}
	dAtA[offset] = uint8(v)
	return base
}
func (m *ValidatorSetChangePacketData) Size() (n int) {
	if m == nil {
		return 0
	}
	var l int
	_ = l
	if len(m.ValidatorUpdates) > 0 {
		for _, e := range m.ValidatorUpdates {
			l = e.Size()
			n += 1 + l + sovCcv(uint64(l))
		}
	}
	if m.ValsetUpdateId != 0 {
		n += 1 + sovCcv(uint64(m.ValsetUpdateId))
	}
	if len(m.SlashAcks) > 0 {
		for _, s := range m.SlashAcks {
			l = len(s)
			n += 1 + l + sovCcv(uint64(l))
		}
	}
	return n
}

func (m *UnbondingOp) Size() (n int) {
	if m == nil {
		return 0
	}
	var l int
	_ = l
	if m.Id != 0 {
		n += 1 + sovCcv(uint64(m.Id))
	}
	if len(m.UnbondingConsumerChains) > 0 {
		for _, s := range m.UnbondingConsumerChains {
			l = len(s)
			n += 1 + l + sovCcv(uint64(l))
		}
	}
	return n
}

func (m *VSCMaturedPacketData) Size() (n int) {
	if m == nil {
		return 0
	}
	var l int
	_ = l
	if m.ValsetUpdateId != 0 {
		n += 1 + sovCcv(uint64(m.ValsetUpdateId))
	}
	return n
}

func (m *SlashPacketData) Size() (n int) {
	if m == nil {
		return 0
	}
	var l int
	_ = l
	l = m.Validator.Size()
	n += 1 + l + sovCcv(uint64(l))
	if m.ValsetUpdateId != 0 {
		n += 1 + sovCcv(uint64(m.ValsetUpdateId))
	}
	if m.Infraction != 0 {
		n += 1 + sovCcv(uint64(m.Infraction))
	}
	return n
}

func (m *UnbondingOpsIndex) Size() (n int) {
	if m == nil {
		return 0
	}
	var l int
	_ = l
	if len(m.Ids) > 0 {
		l = 0
		for _, e := range m.Ids {
			l += sovCcv(uint64(e))
		}
		n += 1 + sovCcv(uint64(l)) + l
	}
	return n
}

func (m *MaturedUnbondingOps) Size() (n int) {
	if m == nil {
		return 0
	}
	var l int
	_ = l
	if len(m.Ids) > 0 {
		l = 0
		for _, e := range m.Ids {
			l += sovCcv(uint64(e))
		}
		n += 1 + sovCcv(uint64(l)) + l
	}
	return n
}

func sovCcv(x uint64) (n int) {
	return (math_bits.Len64(x|1) + 6) / 7
}
func sozCcv(x uint64) (n int) {
	return sovCcv(uint64((x << 1) ^ uint64((int64(x) >> 63))))
}
func (m *ValidatorSetChangePacketData) Unmarshal(dAtA []byte) error {
	l := len(dAtA)
	iNdEx := 0
	for iNdEx < l {
		preIndex := iNdEx
		var wire uint64
		for shift := uint(0); ; shift += 7 {
			if shift >= 64 {
				return ErrIntOverflowCcv
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
			return fmt.Errorf("proto: ValidatorSetChangePacketData: wiretype end group for non-group")
		}
		if fieldNum <= 0 {
			return fmt.Errorf("proto: ValidatorSetChangePacketData: illegal tag %d (wire type %d)", fieldNum, wire)
		}
		switch fieldNum {
		case 1:
			if wireType != 2 {
				return fmt.Errorf("proto: wrong wireType = %d for field ValidatorUpdates", wireType)
			}
			var msglen int
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowCcv
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
				return ErrInvalidLengthCcv
			}
			postIndex := iNdEx + msglen
			if postIndex < 0 {
				return ErrInvalidLengthCcv
			}
			if postIndex > l {
				return io.ErrUnexpectedEOF
			}
			m.ValidatorUpdates = append(m.ValidatorUpdates, types.ValidatorUpdate{})
			if err := m.ValidatorUpdates[len(m.ValidatorUpdates)-1].Unmarshal(dAtA[iNdEx:postIndex]); err != nil {
				return err
			}
			iNdEx = postIndex
		case 2:
			if wireType != 0 {
				return fmt.Errorf("proto: wrong wireType = %d for field ValsetUpdateId", wireType)
			}
			m.ValsetUpdateId = 0
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowCcv
				}
				if iNdEx >= l {
					return io.ErrUnexpectedEOF
				}
				b := dAtA[iNdEx]
				iNdEx++
				m.ValsetUpdateId |= uint64(b&0x7F) << shift
				if b < 0x80 {
					break
				}
			}
		case 3:
			if wireType != 2 {
				return fmt.Errorf("proto: wrong wireType = %d for field SlashAcks", wireType)
			}
			var stringLen uint64
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowCcv
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
				return ErrInvalidLengthCcv
			}
			postIndex := iNdEx + intStringLen
			if postIndex < 0 {
				return ErrInvalidLengthCcv
			}
			if postIndex > l {
				return io.ErrUnexpectedEOF
			}
			m.SlashAcks = append(m.SlashAcks, string(dAtA[iNdEx:postIndex]))
			iNdEx = postIndex
		default:
			iNdEx = preIndex
			skippy, err := skipCcv(dAtA[iNdEx:])
			if err != nil {
				return err
			}
			if (skippy < 0) || (iNdEx+skippy) < 0 {
				return ErrInvalidLengthCcv
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
func (m *UnbondingOp) Unmarshal(dAtA []byte) error {
	l := len(dAtA)
	iNdEx := 0
	for iNdEx < l {
		preIndex := iNdEx
		var wire uint64
		for shift := uint(0); ; shift += 7 {
			if shift >= 64 {
				return ErrIntOverflowCcv
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
			return fmt.Errorf("proto: UnbondingOp: wiretype end group for non-group")
		}
		if fieldNum <= 0 {
			return fmt.Errorf("proto: UnbondingOp: illegal tag %d (wire type %d)", fieldNum, wire)
		}
		switch fieldNum {
		case 1:
			if wireType != 0 {
				return fmt.Errorf("proto: wrong wireType = %d for field Id", wireType)
			}
			m.Id = 0
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowCcv
				}
				if iNdEx >= l {
					return io.ErrUnexpectedEOF
				}
				b := dAtA[iNdEx]
				iNdEx++
				m.Id |= uint64(b&0x7F) << shift
				if b < 0x80 {
					break
				}
			}
		case 2:
			if wireType != 2 {
				return fmt.Errorf("proto: wrong wireType = %d for field UnbondingConsumerChains", wireType)
			}
			var stringLen uint64
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowCcv
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
				return ErrInvalidLengthCcv
			}
			postIndex := iNdEx + intStringLen
			if postIndex < 0 {
				return ErrInvalidLengthCcv
			}
			if postIndex > l {
				return io.ErrUnexpectedEOF
			}
			m.UnbondingConsumerChains = append(m.UnbondingConsumerChains, string(dAtA[iNdEx:postIndex]))
			iNdEx = postIndex
		default:
			iNdEx = preIndex
			skippy, err := skipCcv(dAtA[iNdEx:])
			if err != nil {
				return err
			}
			if (skippy < 0) || (iNdEx+skippy) < 0 {
				return ErrInvalidLengthCcv
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
func (m *VSCMaturedPacketData) Unmarshal(dAtA []byte) error {
	l := len(dAtA)
	iNdEx := 0
	for iNdEx < l {
		preIndex := iNdEx
		var wire uint64
		for shift := uint(0); ; shift += 7 {
			if shift >= 64 {
				return ErrIntOverflowCcv
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
			return fmt.Errorf("proto: VSCMaturedPacketData: wiretype end group for non-group")
		}
		if fieldNum <= 0 {
			return fmt.Errorf("proto: VSCMaturedPacketData: illegal tag %d (wire type %d)", fieldNum, wire)
		}
		switch fieldNum {
		case 1:
			if wireType != 0 {
				return fmt.Errorf("proto: wrong wireType = %d for field ValsetUpdateId", wireType)
			}
			m.ValsetUpdateId = 0
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowCcv
				}
				if iNdEx >= l {
					return io.ErrUnexpectedEOF
				}
				b := dAtA[iNdEx]
				iNdEx++
				m.ValsetUpdateId |= uint64(b&0x7F) << shift
				if b < 0x80 {
					break
				}
			}
		default:
			iNdEx = preIndex
			skippy, err := skipCcv(dAtA[iNdEx:])
			if err != nil {
				return err
			}
			if (skippy < 0) || (iNdEx+skippy) < 0 {
				return ErrInvalidLengthCcv
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
func (m *SlashPacketData) Unmarshal(dAtA []byte) error {
	l := len(dAtA)
	iNdEx := 0
	for iNdEx < l {
		preIndex := iNdEx
		var wire uint64
		for shift := uint(0); ; shift += 7 {
			if shift >= 64 {
				return ErrIntOverflowCcv
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
			return fmt.Errorf("proto: SlashPacketData: wiretype end group for non-group")
		}
		if fieldNum <= 0 {
			return fmt.Errorf("proto: SlashPacketData: illegal tag %d (wire type %d)", fieldNum, wire)
		}
		switch fieldNum {
		case 1:
			if wireType != 2 {
				return fmt.Errorf("proto: wrong wireType = %d for field Validator", wireType)
			}
			var msglen int
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowCcv
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
				return ErrInvalidLengthCcv
			}
			postIndex := iNdEx + msglen
			if postIndex < 0 {
				return ErrInvalidLengthCcv
			}
			if postIndex > l {
				return io.ErrUnexpectedEOF
			}
			if err := m.Validator.Unmarshal(dAtA[iNdEx:postIndex]); err != nil {
				return err
			}
			iNdEx = postIndex
		case 2:
			if wireType != 0 {
				return fmt.Errorf("proto: wrong wireType = %d for field ValsetUpdateId", wireType)
			}
			m.ValsetUpdateId = 0
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowCcv
				}
				if iNdEx >= l {
					return io.ErrUnexpectedEOF
				}
				b := dAtA[iNdEx]
				iNdEx++
				m.ValsetUpdateId |= uint64(b&0x7F) << shift
				if b < 0x80 {
					break
				}
			}
		case 3:
			if wireType != 0 {
				return fmt.Errorf("proto: wrong wireType = %d for field Infraction", wireType)
			}
			m.Infraction = 0
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowCcv
				}
				if iNdEx >= l {
					return io.ErrUnexpectedEOF
				}
				b := dAtA[iNdEx]
				iNdEx++
				m.Infraction |= types1.InfractionType(b&0x7F) << shift
				if b < 0x80 {
					break
				}
			}
		default:
			iNdEx = preIndex
			skippy, err := skipCcv(dAtA[iNdEx:])
			if err != nil {
				return err
			}
			if (skippy < 0) || (iNdEx+skippy) < 0 {
				return ErrInvalidLengthCcv
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
func (m *UnbondingOpsIndex) Unmarshal(dAtA []byte) error {
	l := len(dAtA)
	iNdEx := 0
	for iNdEx < l {
		preIndex := iNdEx
		var wire uint64
		for shift := uint(0); ; shift += 7 {
			if shift >= 64 {
				return ErrIntOverflowCcv
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
			return fmt.Errorf("proto: UnbondingOpsIndex: wiretype end group for non-group")
		}
		if fieldNum <= 0 {
			return fmt.Errorf("proto: UnbondingOpsIndex: illegal tag %d (wire type %d)", fieldNum, wire)
		}
		switch fieldNum {
		case 1:
			if wireType == 0 {
				var v uint64
				for shift := uint(0); ; shift += 7 {
					if shift >= 64 {
						return ErrIntOverflowCcv
					}
					if iNdEx >= l {
						return io.ErrUnexpectedEOF
					}
					b := dAtA[iNdEx]
					iNdEx++
					v |= uint64(b&0x7F) << shift
					if b < 0x80 {
						break
					}
				}
				m.Ids = append(m.Ids, v)
			} else if wireType == 2 {
				var packedLen int
				for shift := uint(0); ; shift += 7 {
					if shift >= 64 {
						return ErrIntOverflowCcv
					}
					if iNdEx >= l {
						return io.ErrUnexpectedEOF
					}
					b := dAtA[iNdEx]
					iNdEx++
					packedLen |= int(b&0x7F) << shift
					if b < 0x80 {
						break
					}
				}
				if packedLen < 0 {
					return ErrInvalidLengthCcv
				}
				postIndex := iNdEx + packedLen
				if postIndex < 0 {
					return ErrInvalidLengthCcv
				}
				if postIndex > l {
					return io.ErrUnexpectedEOF
				}
				var elementCount int
				var count int
				for _, integer := range dAtA[iNdEx:postIndex] {
					if integer < 128 {
						count++
					}
				}
				elementCount = count
				if elementCount != 0 && len(m.Ids) == 0 {
					m.Ids = make([]uint64, 0, elementCount)
				}
				for iNdEx < postIndex {
					var v uint64
					for shift := uint(0); ; shift += 7 {
						if shift >= 64 {
							return ErrIntOverflowCcv
						}
						if iNdEx >= l {
							return io.ErrUnexpectedEOF
						}
						b := dAtA[iNdEx]
						iNdEx++
						v |= uint64(b&0x7F) << shift
						if b < 0x80 {
							break
						}
					}
					m.Ids = append(m.Ids, v)
				}
			} else {
				return fmt.Errorf("proto: wrong wireType = %d for field Ids", wireType)
			}
		default:
			iNdEx = preIndex
			skippy, err := skipCcv(dAtA[iNdEx:])
			if err != nil {
				return err
			}
			if (skippy < 0) || (iNdEx+skippy) < 0 {
				return ErrInvalidLengthCcv
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
func (m *MaturedUnbondingOps) Unmarshal(dAtA []byte) error {
	l := len(dAtA)
	iNdEx := 0
	for iNdEx < l {
		preIndex := iNdEx
		var wire uint64
		for shift := uint(0); ; shift += 7 {
			if shift >= 64 {
				return ErrIntOverflowCcv
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
			return fmt.Errorf("proto: MaturedUnbondingOps: wiretype end group for non-group")
		}
		if fieldNum <= 0 {
			return fmt.Errorf("proto: MaturedUnbondingOps: illegal tag %d (wire type %d)", fieldNum, wire)
		}
		switch fieldNum {
		case 1:
			if wireType == 0 {
				var v uint64
				for shift := uint(0); ; shift += 7 {
					if shift >= 64 {
						return ErrIntOverflowCcv
					}
					if iNdEx >= l {
						return io.ErrUnexpectedEOF
					}
					b := dAtA[iNdEx]
					iNdEx++
					v |= uint64(b&0x7F) << shift
					if b < 0x80 {
						break
					}
				}
				m.Ids = append(m.Ids, v)
			} else if wireType == 2 {
				var packedLen int
				for shift := uint(0); ; shift += 7 {
					if shift >= 64 {
						return ErrIntOverflowCcv
					}
					if iNdEx >= l {
						return io.ErrUnexpectedEOF
					}
					b := dAtA[iNdEx]
					iNdEx++
					packedLen |= int(b&0x7F) << shift
					if b < 0x80 {
						break
					}
				}
				if packedLen < 0 {
					return ErrInvalidLengthCcv
				}
				postIndex := iNdEx + packedLen
				if postIndex < 0 {
					return ErrInvalidLengthCcv
				}
				if postIndex > l {
					return io.ErrUnexpectedEOF
				}
				var elementCount int
				var count int
				for _, integer := range dAtA[iNdEx:postIndex] {
					if integer < 128 {
						count++
					}
				}
				elementCount = count
				if elementCount != 0 && len(m.Ids) == 0 {
					m.Ids = make([]uint64, 0, elementCount)
				}
				for iNdEx < postIndex {
					var v uint64
					for shift := uint(0); ; shift += 7 {
						if shift >= 64 {
							return ErrIntOverflowCcv
						}
						if iNdEx >= l {
							return io.ErrUnexpectedEOF
						}
						b := dAtA[iNdEx]
						iNdEx++
						v |= uint64(b&0x7F) << shift
						if b < 0x80 {
							break
						}
					}
					m.Ids = append(m.Ids, v)
				}
			} else {
				return fmt.Errorf("proto: wrong wireType = %d for field Ids", wireType)
			}
		default:
			iNdEx = preIndex
			skippy, err := skipCcv(dAtA[iNdEx:])
			if err != nil {
				return err
			}
			if (skippy < 0) || (iNdEx+skippy) < 0 {
				return ErrInvalidLengthCcv
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
func skipCcv(dAtA []byte) (n int, err error) {
	l := len(dAtA)
	iNdEx := 0
	depth := 0
	for iNdEx < l {
		var wire uint64
		for shift := uint(0); ; shift += 7 {
			if shift >= 64 {
				return 0, ErrIntOverflowCcv
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
					return 0, ErrIntOverflowCcv
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
					return 0, ErrIntOverflowCcv
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
				return 0, ErrInvalidLengthCcv
			}
			iNdEx += length
		case 3:
			depth++
		case 4:
			if depth == 0 {
				return 0, ErrUnexpectedEndOfGroupCcv
			}
			depth--
		case 5:
			iNdEx += 4
		default:
			return 0, fmt.Errorf("proto: illegal wireType %d", wireType)
		}
		if iNdEx < 0 {
			return 0, ErrInvalidLengthCcv
		}
		if depth == 0 {
			return iNdEx, nil
		}
	}
	return 0, io.ErrUnexpectedEOF
}

var (
	ErrInvalidLengthCcv        = fmt.Errorf("proto: negative length found during unmarshaling")
	ErrIntOverflowCcv          = fmt.Errorf("proto: integer overflow")
	ErrUnexpectedEndOfGroupCcv = fmt.Errorf("proto: unexpected end of group")
)
