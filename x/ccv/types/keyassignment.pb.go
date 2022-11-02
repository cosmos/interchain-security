// Code generated by protoc-gen-gogo. DO NOT EDIT.
// source: interchain_security/ccv/provider/v1/keyassignment.proto

package types

import (
	fmt "fmt"
	_ "github.com/gogo/protobuf/gogoproto"
	proto "github.com/gogo/protobuf/proto"
	crypto "github.com/tendermint/tendermint/proto/tendermint/crypto"
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

type LastUpdateMemo struct {
	ConsumerKey *crypto.PublicKey `protobuf:"bytes,1,opt,name=consumer_key,json=consumerKey,proto3" json:"consumer_key,omitempty"`
	ProviderKey *crypto.PublicKey `protobuf:"bytes,2,opt,name=provider_key,json=providerKey,proto3" json:"provider_key,omitempty"`
	Vscid       uint64            `protobuf:"varint,4,opt,name=vscid,proto3" json:"vscid,omitempty"`
	Power       int64             `protobuf:"varint,5,opt,name=power,proto3" json:"power,omitempty"`
}

func (m *LastUpdateMemo) Reset()         { *m = LastUpdateMemo{} }
func (m *LastUpdateMemo) String() string { return proto.CompactTextString(m) }
func (*LastUpdateMemo) ProtoMessage()    {}
func (*LastUpdateMemo) Descriptor() ([]byte, []int) {
	return fileDescriptor_d36beb32b6cd555b, []int{0}
}
func (m *LastUpdateMemo) XXX_Unmarshal(b []byte) error {
	return m.Unmarshal(b)
}
func (m *LastUpdateMemo) XXX_Marshal(b []byte, deterministic bool) ([]byte, error) {
	if deterministic {
		return xxx_messageInfo_LastUpdateMemo.Marshal(b, m, deterministic)
	} else {
		b = b[:cap(b)]
		n, err := m.MarshalToSizedBuffer(b)
		if err != nil {
			return nil, err
		}
		return b[:n], nil
	}
}
func (m *LastUpdateMemo) XXX_Merge(src proto.Message) {
	xxx_messageInfo_LastUpdateMemo.Merge(m, src)
}
func (m *LastUpdateMemo) XXX_Size() int {
	return m.Size()
}
func (m *LastUpdateMemo) XXX_DiscardUnknown() {
	xxx_messageInfo_LastUpdateMemo.DiscardUnknown(m)
}

var xxx_messageInfo_LastUpdateMemo proto.InternalMessageInfo

func (m *LastUpdateMemo) GetConsumerKey() *crypto.PublicKey {
	if m != nil {
		return m.ConsumerKey
	}
	return nil
}

func (m *LastUpdateMemo) GetProviderKey() *crypto.PublicKey {
	if m != nil {
		return m.ProviderKey
	}
	return nil
}

func (m *LastUpdateMemo) GetVscid() uint64 {
	if m != nil {
		return m.Vscid
	}
	return 0
}

func (m *LastUpdateMemo) GetPower() int64 {
	if m != nil {
		return m.Power
	}
	return 0
}

type ConsAddrToKey struct {
	ConsAddr []byte            `protobuf:"bytes,1,opt,name=cons_addr,json=consAddr,proto3" json:"cons_addr,omitempty"`
	Key      *crypto.PublicKey `protobuf:"bytes,2,opt,name=key,proto3" json:"key,omitempty"`
}

func (m *ConsAddrToKey) Reset()         { *m = ConsAddrToKey{} }
func (m *ConsAddrToKey) String() string { return proto.CompactTextString(m) }
func (*ConsAddrToKey) ProtoMessage()    {}
func (*ConsAddrToKey) Descriptor() ([]byte, []int) {
	return fileDescriptor_d36beb32b6cd555b, []int{1}
}
func (m *ConsAddrToKey) XXX_Unmarshal(b []byte) error {
	return m.Unmarshal(b)
}
func (m *ConsAddrToKey) XXX_Marshal(b []byte, deterministic bool) ([]byte, error) {
	if deterministic {
		return xxx_messageInfo_ConsAddrToKey.Marshal(b, m, deterministic)
	} else {
		b = b[:cap(b)]
		n, err := m.MarshalToSizedBuffer(b)
		if err != nil {
			return nil, err
		}
		return b[:n], nil
	}
}
func (m *ConsAddrToKey) XXX_Merge(src proto.Message) {
	xxx_messageInfo_ConsAddrToKey.Merge(m, src)
}
func (m *ConsAddrToKey) XXX_Size() int {
	return m.Size()
}
func (m *ConsAddrToKey) XXX_DiscardUnknown() {
	xxx_messageInfo_ConsAddrToKey.DiscardUnknown(m)
}

var xxx_messageInfo_ConsAddrToKey proto.InternalMessageInfo

func (m *ConsAddrToKey) GetConsAddr() []byte {
	if m != nil {
		return m.ConsAddr
	}
	return nil
}

func (m *ConsAddrToKey) GetKey() *crypto.PublicKey {
	if m != nil {
		return m.Key
	}
	return nil
}

type KeyToKey struct {
	From *crypto.PublicKey `protobuf:"bytes,1,opt,name=from,proto3" json:"from,omitempty"`
	To   *crypto.PublicKey `protobuf:"bytes,2,opt,name=to,proto3" json:"to,omitempty"`
}

func (m *KeyToKey) Reset()         { *m = KeyToKey{} }
func (m *KeyToKey) String() string { return proto.CompactTextString(m) }
func (*KeyToKey) ProtoMessage()    {}
func (*KeyToKey) Descriptor() ([]byte, []int) {
	return fileDescriptor_d36beb32b6cd555b, []int{2}
}
func (m *KeyToKey) XXX_Unmarshal(b []byte) error {
	return m.Unmarshal(b)
}
func (m *KeyToKey) XXX_Marshal(b []byte, deterministic bool) ([]byte, error) {
	if deterministic {
		return xxx_messageInfo_KeyToKey.Marshal(b, m, deterministic)
	} else {
		b = b[:cap(b)]
		n, err := m.MarshalToSizedBuffer(b)
		if err != nil {
			return nil, err
		}
		return b[:n], nil
	}
}
func (m *KeyToKey) XXX_Merge(src proto.Message) {
	xxx_messageInfo_KeyToKey.Merge(m, src)
}
func (m *KeyToKey) XXX_Size() int {
	return m.Size()
}
func (m *KeyToKey) XXX_DiscardUnknown() {
	xxx_messageInfo_KeyToKey.DiscardUnknown(m)
}

var xxx_messageInfo_KeyToKey proto.InternalMessageInfo

func (m *KeyToKey) GetFrom() *crypto.PublicKey {
	if m != nil {
		return m.From
	}
	return nil
}

func (m *KeyToKey) GetTo() *crypto.PublicKey {
	if m != nil {
		return m.To
	}
	return nil
}

type ConsAddrToLastUpdateMemo struct {
	ConsAddr       []byte          `protobuf:"bytes,1,opt,name=cons_addr,json=consAddr,proto3" json:"cons_addr,omitempty"`
	LastUpdateMemo *LastUpdateMemo `protobuf:"bytes,2,opt,name=last_update_memo,json=lastUpdateMemo,proto3" json:"last_update_memo,omitempty"`
}

func (m *ConsAddrToLastUpdateMemo) Reset()         { *m = ConsAddrToLastUpdateMemo{} }
func (m *ConsAddrToLastUpdateMemo) String() string { return proto.CompactTextString(m) }
func (*ConsAddrToLastUpdateMemo) ProtoMessage()    {}
func (*ConsAddrToLastUpdateMemo) Descriptor() ([]byte, []int) {
	return fileDescriptor_d36beb32b6cd555b, []int{3}
}
func (m *ConsAddrToLastUpdateMemo) XXX_Unmarshal(b []byte) error {
	return m.Unmarshal(b)
}
func (m *ConsAddrToLastUpdateMemo) XXX_Marshal(b []byte, deterministic bool) ([]byte, error) {
	if deterministic {
		return xxx_messageInfo_ConsAddrToLastUpdateMemo.Marshal(b, m, deterministic)
	} else {
		b = b[:cap(b)]
		n, err := m.MarshalToSizedBuffer(b)
		if err != nil {
			return nil, err
		}
		return b[:n], nil
	}
}
func (m *ConsAddrToLastUpdateMemo) XXX_Merge(src proto.Message) {
	xxx_messageInfo_ConsAddrToLastUpdateMemo.Merge(m, src)
}
func (m *ConsAddrToLastUpdateMemo) XXX_Size() int {
	return m.Size()
}
func (m *ConsAddrToLastUpdateMemo) XXX_DiscardUnknown() {
	xxx_messageInfo_ConsAddrToLastUpdateMemo.DiscardUnknown(m)
}

var xxx_messageInfo_ConsAddrToLastUpdateMemo proto.InternalMessageInfo

func (m *ConsAddrToLastUpdateMemo) GetConsAddr() []byte {
	if m != nil {
		return m.ConsAddr
	}
	return nil
}

func (m *ConsAddrToLastUpdateMemo) GetLastUpdateMemo() *LastUpdateMemo {
	if m != nil {
		return m.LastUpdateMemo
	}
	return nil
}

type KeyAssignment struct {
	ProviderConsAddrToConsumerKey    []ConsAddrToKey            `protobuf:"bytes,1,rep,name=provider_cons_addr_to_consumer_key,json=providerConsAddrToConsumerKey,proto3" json:"provider_cons_addr_to_consumer_key"`
	ConsumerKeyToProviderKey         []KeyToKey                 `protobuf:"bytes,2,rep,name=consumer_key_to_provider_key,json=consumerKeyToProviderKey,proto3" json:"consumer_key_to_provider_key"`
	ConsumerConsAddrToLastUpdateMemo []ConsAddrToLastUpdateMemo `protobuf:"bytes,3,rep,name=consumer_cons_addr_to_last_update_memo,json=consumerConsAddrToLastUpdateMemo,proto3" json:"consumer_cons_addr_to_last_update_memo"`
}

func (m *KeyAssignment) Reset()         { *m = KeyAssignment{} }
func (m *KeyAssignment) String() string { return proto.CompactTextString(m) }
func (*KeyAssignment) ProtoMessage()    {}
func (*KeyAssignment) Descriptor() ([]byte, []int) {
	return fileDescriptor_d36beb32b6cd555b, []int{4}
}
func (m *KeyAssignment) XXX_Unmarshal(b []byte) error {
	return m.Unmarshal(b)
}
func (m *KeyAssignment) XXX_Marshal(b []byte, deterministic bool) ([]byte, error) {
	if deterministic {
		return xxx_messageInfo_KeyAssignment.Marshal(b, m, deterministic)
	} else {
		b = b[:cap(b)]
		n, err := m.MarshalToSizedBuffer(b)
		if err != nil {
			return nil, err
		}
		return b[:n], nil
	}
}
func (m *KeyAssignment) XXX_Merge(src proto.Message) {
	xxx_messageInfo_KeyAssignment.Merge(m, src)
}
func (m *KeyAssignment) XXX_Size() int {
	return m.Size()
}
func (m *KeyAssignment) XXX_DiscardUnknown() {
	xxx_messageInfo_KeyAssignment.DiscardUnknown(m)
}

var xxx_messageInfo_KeyAssignment proto.InternalMessageInfo

func (m *KeyAssignment) GetProviderConsAddrToConsumerKey() []ConsAddrToKey {
	if m != nil {
		return m.ProviderConsAddrToConsumerKey
	}
	return nil
}

func (m *KeyAssignment) GetConsumerKeyToProviderKey() []KeyToKey {
	if m != nil {
		return m.ConsumerKeyToProviderKey
	}
	return nil
}

func (m *KeyAssignment) GetConsumerConsAddrToLastUpdateMemo() []ConsAddrToLastUpdateMemo {
	if m != nil {
		return m.ConsumerConsAddrToLastUpdateMemo
	}
	return nil
}

func init() {
	proto.RegisterType((*LastUpdateMemo)(nil), "interchain_security.ccv.provider.v1.LastUpdateMemo")
	proto.RegisterType((*ConsAddrToKey)(nil), "interchain_security.ccv.provider.v1.ConsAddrToKey")
	proto.RegisterType((*KeyToKey)(nil), "interchain_security.ccv.provider.v1.KeyToKey")
	proto.RegisterType((*ConsAddrToLastUpdateMemo)(nil), "interchain_security.ccv.provider.v1.ConsAddrToLastUpdateMemo")
	proto.RegisterType((*KeyAssignment)(nil), "interchain_security.ccv.provider.v1.KeyAssignment")
}

func init() {
	proto.RegisterFile("interchain_security/ccv/provider/v1/keyassignment.proto", fileDescriptor_d36beb32b6cd555b)
}

var fileDescriptor_d36beb32b6cd555b = []byte{
	// 518 bytes of a gzipped FileDescriptorProto
	0x1f, 0x8b, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, 0xff, 0x94, 0x54, 0xcf, 0x6e, 0xd3, 0x4e,
	0x18, 0xcc, 0xc6, 0xe9, 0x4f, 0xfd, 0x6d, 0xda, 0x0a, 0x59, 0x3d, 0x58, 0x25, 0x98, 0xc8, 0x48,
	0x28, 0x07, 0xba, 0x26, 0xe9, 0x81, 0x13, 0x42, 0xa5, 0x47, 0x83, 0x54, 0x59, 0xe5, 0x82, 0x40,
	0x96, 0xb3, 0x5e, 0x52, 0xd3, 0xd8, 0x9f, 0xb5, 0xbb, 0x36, 0xf8, 0xcc, 0x0b, 0x70, 0x81, 0x07,
	0xe0, 0x41, 0x38, 0xf7, 0xd8, 0x23, 0x27, 0x84, 0x92, 0x17, 0x41, 0x6b, 0xc7, 0x4e, 0x1c, 0xfe,
	0xc8, 0xdc, 0xb2, 0xd9, 0xf9, 0x66, 0xe6, 0xf3, 0x8c, 0x16, 0x3f, 0x0a, 0x63, 0xc9, 0x38, 0xbd,
	0xf4, 0xc3, 0xd8, 0x13, 0x8c, 0xa6, 0x3c, 0x94, 0xb9, 0x4d, 0x69, 0x66, 0x27, 0x1c, 0xb2, 0x30,
	0x60, 0xdc, 0xce, 0xc6, 0xf6, 0x15, 0xcb, 0x7d, 0x21, 0xc2, 0x59, 0x1c, 0xb1, 0x58, 0x92, 0x84,
	0x83, 0x04, 0xfd, 0xde, 0x6f, 0x06, 0x09, 0xa5, 0x19, 0xa9, 0x06, 0x49, 0x36, 0x3e, 0x3a, 0x9c,
	0xc1, 0x0c, 0x0a, 0xbc, 0xad, 0x7e, 0x95, 0xa3, 0x47, 0x03, 0xc9, 0xe2, 0x80, 0xf1, 0x28, 0x8c,
	0xa5, 0x4d, 0x79, 0x9e, 0x48, 0x50, 0x0a, 0xa2, 0xbc, 0xb5, 0xbe, 0x22, 0x7c, 0xf0, 0xcc, 0x17,
	0xf2, 0x45, 0x12, 0xf8, 0x92, 0x3d, 0x67, 0x11, 0xe8, 0x4f, 0xf0, 0x1e, 0x85, 0x58, 0xa4, 0x11,
	0xe3, 0xde, 0x15, 0xcb, 0x0d, 0x34, 0x44, 0xa3, 0xfe, 0x64, 0x40, 0xd6, 0x3c, 0xa4, 0xe4, 0x21,
	0xe7, 0xe9, 0x74, 0x1e, 0x52, 0x87, 0xe5, 0x6e, 0xbf, 0x9a, 0x70, 0x58, 0xae, 0x08, 0x2a, 0x5b,
	0x05, 0x41, 0xb7, 0x0d, 0x41, 0x35, 0xa1, 0x08, 0x0e, 0xf1, 0x4e, 0x26, 0x68, 0x18, 0x18, 0xbd,
	0x21, 0x1a, 0xf5, 0xdc, 0xf2, 0xa0, 0xfe, 0x4d, 0xe0, 0x1d, 0xe3, 0xc6, 0xce, 0x10, 0x8d, 0x34,
	0xb7, 0x3c, 0x58, 0xaf, 0xf0, 0xfe, 0x19, 0xc4, 0xe2, 0x34, 0x08, 0xf8, 0x05, 0xa8, 0xe1, 0xdb,
	0xf8, 0x7f, 0x65, 0xc6, 0xf3, 0x83, 0x80, 0x17, 0xde, 0xf7, 0xdc, 0x5d, 0xba, 0x42, 0xe8, 0x04,
	0x6b, 0x6d, 0x1d, 0x29, 0xa0, 0xf5, 0x16, 0xef, 0x3a, 0x2c, 0x2f, 0x89, 0x1f, 0xe2, 0xde, 0x1b,
	0x0e, 0x51, 0xab, 0xef, 0x51, 0x20, 0xf5, 0x07, 0xb8, 0x2b, 0xa1, 0x95, 0x58, 0x57, 0x82, 0xf5,
	0x19, 0x61, 0x63, 0xbd, 0xca, 0x56, 0x28, 0x7f, 0xdd, 0xea, 0x35, 0xbe, 0x35, 0xf7, 0x85, 0xf4,
	0xd2, 0x02, 0xef, 0x45, 0x2c, 0xaa, 0x54, 0x4f, 0x48, 0x8b, 0xe2, 0x90, 0xa6, 0x96, 0x7b, 0x30,
	0x6f, 0x9c, 0xad, 0x2f, 0x1a, 0xde, 0x77, 0x58, 0x7e, 0x5a, 0x97, 0x52, 0xff, 0x80, 0xb0, 0x55,
	0x47, 0x5c, 0xfb, 0xf2, 0x24, 0x78, 0x5b, 0xcd, 0xd1, 0x46, 0xfd, 0xc9, 0xa4, 0x95, 0x87, 0x46,
	0x88, 0x4f, 0x7b, 0xd7, 0xdf, 0xef, 0x76, 0xdc, 0x3b, 0x15, 0x60, 0x7d, 0x79, 0xb6, 0xd1, 0x33,
	0x81, 0x07, 0x9b, 0x72, 0x4a, 0x7e, 0xab, 0x77, 0x4a, 0xfe, 0xb8, 0x95, 0x7c, 0x95, 0xf2, 0x4a,
	0xd9, 0xd8, 0xe8, 0xf3, 0x05, 0x9c, 0x6f, 0x74, 0xf3, 0x13, 0xc2, 0xf7, 0x6b, 0xd5, 0xc6, 0xea,
	0xbf, 0x44, 0xa0, 0x15, 0xfa, 0x8f, 0xff, 0x71, 0xfd, 0x66, 0x18, 0x2b, 0x3f, 0xc3, 0x4a, 0xf2,
	0x8f, 0x38, 0xe7, 0x7a, 0x61, 0xa2, 0x9b, 0x85, 0x89, 0x7e, 0x2c, 0x4c, 0xf4, 0x71, 0x69, 0x76,
	0x6e, 0x96, 0x66, 0xe7, 0xdb, 0xd2, 0xec, 0xbc, 0x1c, 0xcf, 0x42, 0x79, 0x99, 0x4e, 0x09, 0x85,
	0xc8, 0xa6, 0x20, 0x22, 0x10, 0xf6, 0xda, 0xd1, 0x71, 0xfd, 0x0c, 0xbd, 0x2f, 0x1e, 0x22, 0x99,
	0x27, 0x4c, 0x4c, 0xff, 0x2b, 0x1e, 0x87, 0x93, 0x9f, 0x01, 0x00, 0x00, 0xff, 0xff, 0xfc, 0x3d,
	0x9f, 0xe7, 0xb0, 0x04, 0x00, 0x00,
}

func (m *LastUpdateMemo) Marshal() (dAtA []byte, err error) {
	size := m.Size()
	dAtA = make([]byte, size)
	n, err := m.MarshalToSizedBuffer(dAtA[:size])
	if err != nil {
		return nil, err
	}
	return dAtA[:n], nil
}

func (m *LastUpdateMemo) MarshalTo(dAtA []byte) (int, error) {
	size := m.Size()
	return m.MarshalToSizedBuffer(dAtA[:size])
}

func (m *LastUpdateMemo) MarshalToSizedBuffer(dAtA []byte) (int, error) {
	i := len(dAtA)
	_ = i
	var l int
	_ = l
	if m.Power != 0 {
		i = encodeVarintKeyassignment(dAtA, i, uint64(m.Power))
		i--
		dAtA[i] = 0x28
	}
	if m.Vscid != 0 {
		i = encodeVarintKeyassignment(dAtA, i, uint64(m.Vscid))
		i--
		dAtA[i] = 0x20
	}
	if m.ProviderKey != nil {
		{
			size, err := m.ProviderKey.MarshalToSizedBuffer(dAtA[:i])
			if err != nil {
				return 0, err
			}
			i -= size
			i = encodeVarintKeyassignment(dAtA, i, uint64(size))
		}
		i--
		dAtA[i] = 0x12
	}
	if m.ConsumerKey != nil {
		{
			size, err := m.ConsumerKey.MarshalToSizedBuffer(dAtA[:i])
			if err != nil {
				return 0, err
			}
			i -= size
			i = encodeVarintKeyassignment(dAtA, i, uint64(size))
		}
		i--
		dAtA[i] = 0xa
	}
	return len(dAtA) - i, nil
}

func (m *ConsAddrToKey) Marshal() (dAtA []byte, err error) {
	size := m.Size()
	dAtA = make([]byte, size)
	n, err := m.MarshalToSizedBuffer(dAtA[:size])
	if err != nil {
		return nil, err
	}
	return dAtA[:n], nil
}

func (m *ConsAddrToKey) MarshalTo(dAtA []byte) (int, error) {
	size := m.Size()
	return m.MarshalToSizedBuffer(dAtA[:size])
}

func (m *ConsAddrToKey) MarshalToSizedBuffer(dAtA []byte) (int, error) {
	i := len(dAtA)
	_ = i
	var l int
	_ = l
	if m.Key != nil {
		{
			size, err := m.Key.MarshalToSizedBuffer(dAtA[:i])
			if err != nil {
				return 0, err
			}
			i -= size
			i = encodeVarintKeyassignment(dAtA, i, uint64(size))
		}
		i--
		dAtA[i] = 0x12
	}
	if len(m.ConsAddr) > 0 {
		i -= len(m.ConsAddr)
		copy(dAtA[i:], m.ConsAddr)
		i = encodeVarintKeyassignment(dAtA, i, uint64(len(m.ConsAddr)))
		i--
		dAtA[i] = 0xa
	}
	return len(dAtA) - i, nil
}

func (m *KeyToKey) Marshal() (dAtA []byte, err error) {
	size := m.Size()
	dAtA = make([]byte, size)
	n, err := m.MarshalToSizedBuffer(dAtA[:size])
	if err != nil {
		return nil, err
	}
	return dAtA[:n], nil
}

func (m *KeyToKey) MarshalTo(dAtA []byte) (int, error) {
	size := m.Size()
	return m.MarshalToSizedBuffer(dAtA[:size])
}

func (m *KeyToKey) MarshalToSizedBuffer(dAtA []byte) (int, error) {
	i := len(dAtA)
	_ = i
	var l int
	_ = l
	if m.To != nil {
		{
			size, err := m.To.MarshalToSizedBuffer(dAtA[:i])
			if err != nil {
				return 0, err
			}
			i -= size
			i = encodeVarintKeyassignment(dAtA, i, uint64(size))
		}
		i--
		dAtA[i] = 0x12
	}
	if m.From != nil {
		{
			size, err := m.From.MarshalToSizedBuffer(dAtA[:i])
			if err != nil {
				return 0, err
			}
			i -= size
			i = encodeVarintKeyassignment(dAtA, i, uint64(size))
		}
		i--
		dAtA[i] = 0xa
	}
	return len(dAtA) - i, nil
}

func (m *ConsAddrToLastUpdateMemo) Marshal() (dAtA []byte, err error) {
	size := m.Size()
	dAtA = make([]byte, size)
	n, err := m.MarshalToSizedBuffer(dAtA[:size])
	if err != nil {
		return nil, err
	}
	return dAtA[:n], nil
}

func (m *ConsAddrToLastUpdateMemo) MarshalTo(dAtA []byte) (int, error) {
	size := m.Size()
	return m.MarshalToSizedBuffer(dAtA[:size])
}

func (m *ConsAddrToLastUpdateMemo) MarshalToSizedBuffer(dAtA []byte) (int, error) {
	i := len(dAtA)
	_ = i
	var l int
	_ = l
	if m.LastUpdateMemo != nil {
		{
			size, err := m.LastUpdateMemo.MarshalToSizedBuffer(dAtA[:i])
			if err != nil {
				return 0, err
			}
			i -= size
			i = encodeVarintKeyassignment(dAtA, i, uint64(size))
		}
		i--
		dAtA[i] = 0x12
	}
	if len(m.ConsAddr) > 0 {
		i -= len(m.ConsAddr)
		copy(dAtA[i:], m.ConsAddr)
		i = encodeVarintKeyassignment(dAtA, i, uint64(len(m.ConsAddr)))
		i--
		dAtA[i] = 0xa
	}
	return len(dAtA) - i, nil
}

func (m *KeyAssignment) Marshal() (dAtA []byte, err error) {
	size := m.Size()
	dAtA = make([]byte, size)
	n, err := m.MarshalToSizedBuffer(dAtA[:size])
	if err != nil {
		return nil, err
	}
	return dAtA[:n], nil
}

func (m *KeyAssignment) MarshalTo(dAtA []byte) (int, error) {
	size := m.Size()
	return m.MarshalToSizedBuffer(dAtA[:size])
}

func (m *KeyAssignment) MarshalToSizedBuffer(dAtA []byte) (int, error) {
	i := len(dAtA)
	_ = i
	var l int
	_ = l
	if len(m.ConsumerConsAddrToLastUpdateMemo) > 0 {
		for iNdEx := len(m.ConsumerConsAddrToLastUpdateMemo) - 1; iNdEx >= 0; iNdEx-- {
			{
				size, err := m.ConsumerConsAddrToLastUpdateMemo[iNdEx].MarshalToSizedBuffer(dAtA[:i])
				if err != nil {
					return 0, err
				}
				i -= size
				i = encodeVarintKeyassignment(dAtA, i, uint64(size))
			}
			i--
			dAtA[i] = 0x1a
		}
	}
	if len(m.ConsumerKeyToProviderKey) > 0 {
		for iNdEx := len(m.ConsumerKeyToProviderKey) - 1; iNdEx >= 0; iNdEx-- {
			{
				size, err := m.ConsumerKeyToProviderKey[iNdEx].MarshalToSizedBuffer(dAtA[:i])
				if err != nil {
					return 0, err
				}
				i -= size
				i = encodeVarintKeyassignment(dAtA, i, uint64(size))
			}
			i--
			dAtA[i] = 0x12
		}
	}
	if len(m.ProviderConsAddrToConsumerKey) > 0 {
		for iNdEx := len(m.ProviderConsAddrToConsumerKey) - 1; iNdEx >= 0; iNdEx-- {
			{
				size, err := m.ProviderConsAddrToConsumerKey[iNdEx].MarshalToSizedBuffer(dAtA[:i])
				if err != nil {
					return 0, err
				}
				i -= size
				i = encodeVarintKeyassignment(dAtA, i, uint64(size))
			}
			i--
			dAtA[i] = 0xa
		}
	}
	return len(dAtA) - i, nil
}

func encodeVarintKeyassignment(dAtA []byte, offset int, v uint64) int {
	offset -= sovKeyassignment(v)
	base := offset
	for v >= 1<<7 {
		dAtA[offset] = uint8(v&0x7f | 0x80)
		v >>= 7
		offset++
	}
	dAtA[offset] = uint8(v)
	return base
}
func (m *LastUpdateMemo) Size() (n int) {
	if m == nil {
		return 0
	}
	var l int
	_ = l
	if m.ConsumerKey != nil {
		l = m.ConsumerKey.Size()
		n += 1 + l + sovKeyassignment(uint64(l))
	}
	if m.ProviderKey != nil {
		l = m.ProviderKey.Size()
		n += 1 + l + sovKeyassignment(uint64(l))
	}
	if m.Vscid != 0 {
		n += 1 + sovKeyassignment(uint64(m.Vscid))
	}
	if m.Power != 0 {
		n += 1 + sovKeyassignment(uint64(m.Power))
	}
	return n
}

func (m *ConsAddrToKey) Size() (n int) {
	if m == nil {
		return 0
	}
	var l int
	_ = l
	l = len(m.ConsAddr)
	if l > 0 {
		n += 1 + l + sovKeyassignment(uint64(l))
	}
	if m.Key != nil {
		l = m.Key.Size()
		n += 1 + l + sovKeyassignment(uint64(l))
	}
	return n
}

func (m *KeyToKey) Size() (n int) {
	if m == nil {
		return 0
	}
	var l int
	_ = l
	if m.From != nil {
		l = m.From.Size()
		n += 1 + l + sovKeyassignment(uint64(l))
	}
	if m.To != nil {
		l = m.To.Size()
		n += 1 + l + sovKeyassignment(uint64(l))
	}
	return n
}

func (m *ConsAddrToLastUpdateMemo) Size() (n int) {
	if m == nil {
		return 0
	}
	var l int
	_ = l
	l = len(m.ConsAddr)
	if l > 0 {
		n += 1 + l + sovKeyassignment(uint64(l))
	}
	if m.LastUpdateMemo != nil {
		l = m.LastUpdateMemo.Size()
		n += 1 + l + sovKeyassignment(uint64(l))
	}
	return n
}

func (m *KeyAssignment) Size() (n int) {
	if m == nil {
		return 0
	}
	var l int
	_ = l
	if len(m.ProviderConsAddrToConsumerKey) > 0 {
		for _, e := range m.ProviderConsAddrToConsumerKey {
			l = e.Size()
			n += 1 + l + sovKeyassignment(uint64(l))
		}
	}
	if len(m.ConsumerKeyToProviderKey) > 0 {
		for _, e := range m.ConsumerKeyToProviderKey {
			l = e.Size()
			n += 1 + l + sovKeyassignment(uint64(l))
		}
	}
	if len(m.ConsumerConsAddrToLastUpdateMemo) > 0 {
		for _, e := range m.ConsumerConsAddrToLastUpdateMemo {
			l = e.Size()
			n += 1 + l + sovKeyassignment(uint64(l))
		}
	}
	return n
}

func sovKeyassignment(x uint64) (n int) {
	return (math_bits.Len64(x|1) + 6) / 7
}
func sozKeyassignment(x uint64) (n int) {
	return sovKeyassignment(uint64((x << 1) ^ uint64((int64(x) >> 63))))
}
func (m *LastUpdateMemo) Unmarshal(dAtA []byte) error {
	l := len(dAtA)
	iNdEx := 0
	for iNdEx < l {
		preIndex := iNdEx
		var wire uint64
		for shift := uint(0); ; shift += 7 {
			if shift >= 64 {
				return ErrIntOverflowKeyassignment
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
			return fmt.Errorf("proto: LastUpdateMemo: wiretype end group for non-group")
		}
		if fieldNum <= 0 {
			return fmt.Errorf("proto: LastUpdateMemo: illegal tag %d (wire type %d)", fieldNum, wire)
		}
		switch fieldNum {
		case 1:
			if wireType != 2 {
				return fmt.Errorf("proto: wrong wireType = %d for field ConsumerKey", wireType)
			}
			var msglen int
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowKeyassignment
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
				return ErrInvalidLengthKeyassignment
			}
			postIndex := iNdEx + msglen
			if postIndex < 0 {
				return ErrInvalidLengthKeyassignment
			}
			if postIndex > l {
				return io.ErrUnexpectedEOF
			}
			if m.ConsumerKey == nil {
				m.ConsumerKey = &crypto.PublicKey{}
			}
			if err := m.ConsumerKey.Unmarshal(dAtA[iNdEx:postIndex]); err != nil {
				return err
			}
			iNdEx = postIndex
		case 2:
			if wireType != 2 {
				return fmt.Errorf("proto: wrong wireType = %d for field ProviderKey", wireType)
			}
			var msglen int
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowKeyassignment
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
				return ErrInvalidLengthKeyassignment
			}
			postIndex := iNdEx + msglen
			if postIndex < 0 {
				return ErrInvalidLengthKeyassignment
			}
			if postIndex > l {
				return io.ErrUnexpectedEOF
			}
			if m.ProviderKey == nil {
				m.ProviderKey = &crypto.PublicKey{}
			}
			if err := m.ProviderKey.Unmarshal(dAtA[iNdEx:postIndex]); err != nil {
				return err
			}
			iNdEx = postIndex
		case 4:
			if wireType != 0 {
				return fmt.Errorf("proto: wrong wireType = %d for field Vscid", wireType)
			}
			m.Vscid = 0
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowKeyassignment
				}
				if iNdEx >= l {
					return io.ErrUnexpectedEOF
				}
				b := dAtA[iNdEx]
				iNdEx++
				m.Vscid |= uint64(b&0x7F) << shift
				if b < 0x80 {
					break
				}
			}
		case 5:
			if wireType != 0 {
				return fmt.Errorf("proto: wrong wireType = %d for field Power", wireType)
			}
			m.Power = 0
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowKeyassignment
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
			skippy, err := skipKeyassignment(dAtA[iNdEx:])
			if err != nil {
				return err
			}
			if (skippy < 0) || (iNdEx+skippy) < 0 {
				return ErrInvalidLengthKeyassignment
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
func (m *ConsAddrToKey) Unmarshal(dAtA []byte) error {
	l := len(dAtA)
	iNdEx := 0
	for iNdEx < l {
		preIndex := iNdEx
		var wire uint64
		for shift := uint(0); ; shift += 7 {
			if shift >= 64 {
				return ErrIntOverflowKeyassignment
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
			return fmt.Errorf("proto: ConsAddrToKey: wiretype end group for non-group")
		}
		if fieldNum <= 0 {
			return fmt.Errorf("proto: ConsAddrToKey: illegal tag %d (wire type %d)", fieldNum, wire)
		}
		switch fieldNum {
		case 1:
			if wireType != 2 {
				return fmt.Errorf("proto: wrong wireType = %d for field ConsAddr", wireType)
			}
			var byteLen int
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowKeyassignment
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
				return ErrInvalidLengthKeyassignment
			}
			postIndex := iNdEx + byteLen
			if postIndex < 0 {
				return ErrInvalidLengthKeyassignment
			}
			if postIndex > l {
				return io.ErrUnexpectedEOF
			}
			m.ConsAddr = append(m.ConsAddr[:0], dAtA[iNdEx:postIndex]...)
			if m.ConsAddr == nil {
				m.ConsAddr = []byte{}
			}
			iNdEx = postIndex
		case 2:
			if wireType != 2 {
				return fmt.Errorf("proto: wrong wireType = %d for field Key", wireType)
			}
			var msglen int
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowKeyassignment
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
				return ErrInvalidLengthKeyassignment
			}
			postIndex := iNdEx + msglen
			if postIndex < 0 {
				return ErrInvalidLengthKeyassignment
			}
			if postIndex > l {
				return io.ErrUnexpectedEOF
			}
			if m.Key == nil {
				m.Key = &crypto.PublicKey{}
			}
			if err := m.Key.Unmarshal(dAtA[iNdEx:postIndex]); err != nil {
				return err
			}
			iNdEx = postIndex
		default:
			iNdEx = preIndex
			skippy, err := skipKeyassignment(dAtA[iNdEx:])
			if err != nil {
				return err
			}
			if (skippy < 0) || (iNdEx+skippy) < 0 {
				return ErrInvalidLengthKeyassignment
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
func (m *KeyToKey) Unmarshal(dAtA []byte) error {
	l := len(dAtA)
	iNdEx := 0
	for iNdEx < l {
		preIndex := iNdEx
		var wire uint64
		for shift := uint(0); ; shift += 7 {
			if shift >= 64 {
				return ErrIntOverflowKeyassignment
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
			return fmt.Errorf("proto: KeyToKey: wiretype end group for non-group")
		}
		if fieldNum <= 0 {
			return fmt.Errorf("proto: KeyToKey: illegal tag %d (wire type %d)", fieldNum, wire)
		}
		switch fieldNum {
		case 1:
			if wireType != 2 {
				return fmt.Errorf("proto: wrong wireType = %d for field From", wireType)
			}
			var msglen int
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowKeyassignment
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
				return ErrInvalidLengthKeyassignment
			}
			postIndex := iNdEx + msglen
			if postIndex < 0 {
				return ErrInvalidLengthKeyassignment
			}
			if postIndex > l {
				return io.ErrUnexpectedEOF
			}
			if m.From == nil {
				m.From = &crypto.PublicKey{}
			}
			if err := m.From.Unmarshal(dAtA[iNdEx:postIndex]); err != nil {
				return err
			}
			iNdEx = postIndex
		case 2:
			if wireType != 2 {
				return fmt.Errorf("proto: wrong wireType = %d for field To", wireType)
			}
			var msglen int
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowKeyassignment
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
				return ErrInvalidLengthKeyassignment
			}
			postIndex := iNdEx + msglen
			if postIndex < 0 {
				return ErrInvalidLengthKeyassignment
			}
			if postIndex > l {
				return io.ErrUnexpectedEOF
			}
			if m.To == nil {
				m.To = &crypto.PublicKey{}
			}
			if err := m.To.Unmarshal(dAtA[iNdEx:postIndex]); err != nil {
				return err
			}
			iNdEx = postIndex
		default:
			iNdEx = preIndex
			skippy, err := skipKeyassignment(dAtA[iNdEx:])
			if err != nil {
				return err
			}
			if (skippy < 0) || (iNdEx+skippy) < 0 {
				return ErrInvalidLengthKeyassignment
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
func (m *ConsAddrToLastUpdateMemo) Unmarshal(dAtA []byte) error {
	l := len(dAtA)
	iNdEx := 0
	for iNdEx < l {
		preIndex := iNdEx
		var wire uint64
		for shift := uint(0); ; shift += 7 {
			if shift >= 64 {
				return ErrIntOverflowKeyassignment
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
			return fmt.Errorf("proto: ConsAddrToLastUpdateMemo: wiretype end group for non-group")
		}
		if fieldNum <= 0 {
			return fmt.Errorf("proto: ConsAddrToLastUpdateMemo: illegal tag %d (wire type %d)", fieldNum, wire)
		}
		switch fieldNum {
		case 1:
			if wireType != 2 {
				return fmt.Errorf("proto: wrong wireType = %d for field ConsAddr", wireType)
			}
			var byteLen int
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowKeyassignment
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
				return ErrInvalidLengthKeyassignment
			}
			postIndex := iNdEx + byteLen
			if postIndex < 0 {
				return ErrInvalidLengthKeyassignment
			}
			if postIndex > l {
				return io.ErrUnexpectedEOF
			}
			m.ConsAddr = append(m.ConsAddr[:0], dAtA[iNdEx:postIndex]...)
			if m.ConsAddr == nil {
				m.ConsAddr = []byte{}
			}
			iNdEx = postIndex
		case 2:
			if wireType != 2 {
				return fmt.Errorf("proto: wrong wireType = %d for field LastUpdateMemo", wireType)
			}
			var msglen int
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowKeyassignment
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
				return ErrInvalidLengthKeyassignment
			}
			postIndex := iNdEx + msglen
			if postIndex < 0 {
				return ErrInvalidLengthKeyassignment
			}
			if postIndex > l {
				return io.ErrUnexpectedEOF
			}
			if m.LastUpdateMemo == nil {
				m.LastUpdateMemo = &LastUpdateMemo{}
			}
			if err := m.LastUpdateMemo.Unmarshal(dAtA[iNdEx:postIndex]); err != nil {
				return err
			}
			iNdEx = postIndex
		default:
			iNdEx = preIndex
			skippy, err := skipKeyassignment(dAtA[iNdEx:])
			if err != nil {
				return err
			}
			if (skippy < 0) || (iNdEx+skippy) < 0 {
				return ErrInvalidLengthKeyassignment
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
func (m *KeyAssignment) Unmarshal(dAtA []byte) error {
	l := len(dAtA)
	iNdEx := 0
	for iNdEx < l {
		preIndex := iNdEx
		var wire uint64
		for shift := uint(0); ; shift += 7 {
			if shift >= 64 {
				return ErrIntOverflowKeyassignment
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
			return fmt.Errorf("proto: KeyAssignment: wiretype end group for non-group")
		}
		if fieldNum <= 0 {
			return fmt.Errorf("proto: KeyAssignment: illegal tag %d (wire type %d)", fieldNum, wire)
		}
		switch fieldNum {
		case 1:
			if wireType != 2 {
				return fmt.Errorf("proto: wrong wireType = %d for field ProviderConsAddrToConsumerKey", wireType)
			}
			var msglen int
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowKeyassignment
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
				return ErrInvalidLengthKeyassignment
			}
			postIndex := iNdEx + msglen
			if postIndex < 0 {
				return ErrInvalidLengthKeyassignment
			}
			if postIndex > l {
				return io.ErrUnexpectedEOF
			}
			m.ProviderConsAddrToConsumerKey = append(m.ProviderConsAddrToConsumerKey, ConsAddrToKey{})
			if err := m.ProviderConsAddrToConsumerKey[len(m.ProviderConsAddrToConsumerKey)-1].Unmarshal(dAtA[iNdEx:postIndex]); err != nil {
				return err
			}
			iNdEx = postIndex
		case 2:
			if wireType != 2 {
				return fmt.Errorf("proto: wrong wireType = %d for field ConsumerKeyToProviderKey", wireType)
			}
			var msglen int
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowKeyassignment
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
				return ErrInvalidLengthKeyassignment
			}
			postIndex := iNdEx + msglen
			if postIndex < 0 {
				return ErrInvalidLengthKeyassignment
			}
			if postIndex > l {
				return io.ErrUnexpectedEOF
			}
			m.ConsumerKeyToProviderKey = append(m.ConsumerKeyToProviderKey, KeyToKey{})
			if err := m.ConsumerKeyToProviderKey[len(m.ConsumerKeyToProviderKey)-1].Unmarshal(dAtA[iNdEx:postIndex]); err != nil {
				return err
			}
			iNdEx = postIndex
		case 3:
			if wireType != 2 {
				return fmt.Errorf("proto: wrong wireType = %d for field ConsumerConsAddrToLastUpdateMemo", wireType)
			}
			var msglen int
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowKeyassignment
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
				return ErrInvalidLengthKeyassignment
			}
			postIndex := iNdEx + msglen
			if postIndex < 0 {
				return ErrInvalidLengthKeyassignment
			}
			if postIndex > l {
				return io.ErrUnexpectedEOF
			}
			m.ConsumerConsAddrToLastUpdateMemo = append(m.ConsumerConsAddrToLastUpdateMemo, ConsAddrToLastUpdateMemo{})
			if err := m.ConsumerConsAddrToLastUpdateMemo[len(m.ConsumerConsAddrToLastUpdateMemo)-1].Unmarshal(dAtA[iNdEx:postIndex]); err != nil {
				return err
			}
			iNdEx = postIndex
		default:
			iNdEx = preIndex
			skippy, err := skipKeyassignment(dAtA[iNdEx:])
			if err != nil {
				return err
			}
			if (skippy < 0) || (iNdEx+skippy) < 0 {
				return ErrInvalidLengthKeyassignment
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
func skipKeyassignment(dAtA []byte) (n int, err error) {
	l := len(dAtA)
	iNdEx := 0
	depth := 0
	for iNdEx < l {
		var wire uint64
		for shift := uint(0); ; shift += 7 {
			if shift >= 64 {
				return 0, ErrIntOverflowKeyassignment
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
					return 0, ErrIntOverflowKeyassignment
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
					return 0, ErrIntOverflowKeyassignment
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
				return 0, ErrInvalidLengthKeyassignment
			}
			iNdEx += length
		case 3:
			depth++
		case 4:
			if depth == 0 {
				return 0, ErrUnexpectedEndOfGroupKeyassignment
			}
			depth--
		case 5:
			iNdEx += 4
		default:
			return 0, fmt.Errorf("proto: illegal wireType %d", wireType)
		}
		if iNdEx < 0 {
			return 0, ErrInvalidLengthKeyassignment
		}
		if depth == 0 {
			return iNdEx, nil
		}
	}
	return 0, io.ErrUnexpectedEOF
}

var (
	ErrInvalidLengthKeyassignment        = fmt.Errorf("proto: negative length found during unmarshaling")
	ErrIntOverflowKeyassignment          = fmt.Errorf("proto: integer overflow")
	ErrUnexpectedEndOfGroupKeyassignment = fmt.Errorf("proto: unexpected end of group")
)
