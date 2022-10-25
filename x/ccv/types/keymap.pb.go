// Code generated by protoc-gen-gogo. DO NOT EDIT.
// source: interchain_security/ccv/provider/v1/keymap.proto

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
	Ck    *crypto.PublicKey `protobuf:"bytes,1,opt,name=ck,proto3" json:"ck,omitempty"`
	Pk    *crypto.PublicKey `protobuf:"bytes,2,opt,name=pk,proto3" json:"pk,omitempty"`
	Cca   []byte            `protobuf:"bytes,3,opt,name=cca,proto3" json:"cca,omitempty"`
	Vscid uint64            `protobuf:"varint,4,opt,name=vscid,proto3" json:"vscid,omitempty"`
	Power int64             `protobuf:"varint,5,opt,name=power,proto3" json:"power,omitempty"`
}

func (m *LastUpdateMemo) Reset()         { *m = LastUpdateMemo{} }
func (m *LastUpdateMemo) String() string { return proto.CompactTextString(m) }
func (*LastUpdateMemo) ProtoMessage()    {}
func (*LastUpdateMemo) Descriptor() ([]byte, []int) {
	return fileDescriptor_864a04a770548246, []int{0}
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

func (m *LastUpdateMemo) GetCk() *crypto.PublicKey {
	if m != nil {
		return m.Ck
	}
	return nil
}

func (m *LastUpdateMemo) GetPk() *crypto.PublicKey {
	if m != nil {
		return m.Pk
	}
	return nil
}

func (m *LastUpdateMemo) GetCca() []byte {
	if m != nil {
		return m.Cca
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

type KeyToKey struct {
	From *crypto.PublicKey `protobuf:"bytes,1,opt,name=from,proto3" json:"from,omitempty"`
	To   *crypto.PublicKey `protobuf:"bytes,2,opt,name=to,proto3" json:"to,omitempty"`
}

func (m *KeyToKey) Reset()         { *m = KeyToKey{} }
func (m *KeyToKey) String() string { return proto.CompactTextString(m) }
func (*KeyToKey) ProtoMessage()    {}
func (*KeyToKey) Descriptor() ([]byte, []int) {
	return fileDescriptor_864a04a770548246, []int{1}
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

type KeyToLastUpdateMemo struct {
	Key            *crypto.PublicKey `protobuf:"bytes,1,opt,name=key,proto3" json:"key,omitempty"`
	LastUpdateMemo *LastUpdateMemo   `protobuf:"bytes,2,opt,name=last_update_memo,json=lastUpdateMemo,proto3" json:"last_update_memo,omitempty"`
}

func (m *KeyToLastUpdateMemo) Reset()         { *m = KeyToLastUpdateMemo{} }
func (m *KeyToLastUpdateMemo) String() string { return proto.CompactTextString(m) }
func (*KeyToLastUpdateMemo) ProtoMessage()    {}
func (*KeyToLastUpdateMemo) Descriptor() ([]byte, []int) {
	return fileDescriptor_864a04a770548246, []int{2}
}
func (m *KeyToLastUpdateMemo) XXX_Unmarshal(b []byte) error {
	return m.Unmarshal(b)
}
func (m *KeyToLastUpdateMemo) XXX_Marshal(b []byte, deterministic bool) ([]byte, error) {
	if deterministic {
		return xxx_messageInfo_KeyToLastUpdateMemo.Marshal(b, m, deterministic)
	} else {
		b = b[:cap(b)]
		n, err := m.MarshalToSizedBuffer(b)
		if err != nil {
			return nil, err
		}
		return b[:n], nil
	}
}
func (m *KeyToLastUpdateMemo) XXX_Merge(src proto.Message) {
	xxx_messageInfo_KeyToLastUpdateMemo.Merge(m, src)
}
func (m *KeyToLastUpdateMemo) XXX_Size() int {
	return m.Size()
}
func (m *KeyToLastUpdateMemo) XXX_DiscardUnknown() {
	xxx_messageInfo_KeyToLastUpdateMemo.DiscardUnknown(m)
}

var xxx_messageInfo_KeyToLastUpdateMemo proto.InternalMessageInfo

func (m *KeyToLastUpdateMemo) GetKey() *crypto.PublicKey {
	if m != nil {
		return m.Key
	}
	return nil
}

func (m *KeyToLastUpdateMemo) GetLastUpdateMemo() *LastUpdateMemo {
	if m != nil {
		return m.LastUpdateMemo
	}
	return nil
}

type ConsAddrToKey struct {
	ConsAddr []byte            `protobuf:"bytes,1,opt,name=cons_addr,json=consAddr,proto3" json:"cons_addr,omitempty"`
	Key      *crypto.PublicKey `protobuf:"bytes,2,opt,name=key,proto3" json:"key,omitempty"`
}

func (m *ConsAddrToKey) Reset()         { *m = ConsAddrToKey{} }
func (m *ConsAddrToKey) String() string { return proto.CompactTextString(m) }
func (*ConsAddrToKey) ProtoMessage()    {}
func (*ConsAddrToKey) Descriptor() ([]byte, []int) {
	return fileDescriptor_864a04a770548246, []int{3}
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

type KeyMap struct {
	PkToCk             []KeyToKey            `protobuf:"bytes,1,rep,name=pk_to_ck,json=pkToCk,proto3" json:"pk_to_ck"`
	CkToPk             []KeyToKey            `protobuf:"bytes,2,rep,name=ck_to_pk,json=ckToPk,proto3" json:"ck_to_pk"`
	CkToLastUpdateMemo []KeyToLastUpdateMemo `protobuf:"bytes,3,rep,name=ck_to_last_update_memo,json=ckToLastUpdateMemo,proto3" json:"ck_to_last_update_memo"`
	CcaToCk            []ConsAddrToKey       `protobuf:"bytes,4,rep,name=cca_to_ck,json=ccaToCk,proto3" json:"cca_to_ck"`
}

func (m *KeyMap) Reset()         { *m = KeyMap{} }
func (m *KeyMap) String() string { return proto.CompactTextString(m) }
func (*KeyMap) ProtoMessage()    {}
func (*KeyMap) Descriptor() ([]byte, []int) {
	return fileDescriptor_864a04a770548246, []int{4}
}
func (m *KeyMap) XXX_Unmarshal(b []byte) error {
	return m.Unmarshal(b)
}
func (m *KeyMap) XXX_Marshal(b []byte, deterministic bool) ([]byte, error) {
	if deterministic {
		return xxx_messageInfo_KeyMap.Marshal(b, m, deterministic)
	} else {
		b = b[:cap(b)]
		n, err := m.MarshalToSizedBuffer(b)
		if err != nil {
			return nil, err
		}
		return b[:n], nil
	}
}
func (m *KeyMap) XXX_Merge(src proto.Message) {
	xxx_messageInfo_KeyMap.Merge(m, src)
}
func (m *KeyMap) XXX_Size() int {
	return m.Size()
}
func (m *KeyMap) XXX_DiscardUnknown() {
	xxx_messageInfo_KeyMap.DiscardUnknown(m)
}

var xxx_messageInfo_KeyMap proto.InternalMessageInfo

func (m *KeyMap) GetPkToCk() []KeyToKey {
	if m != nil {
		return m.PkToCk
	}
	return nil
}

func (m *KeyMap) GetCkToPk() []KeyToKey {
	if m != nil {
		return m.CkToPk
	}
	return nil
}

func (m *KeyMap) GetCkToLastUpdateMemo() []KeyToLastUpdateMemo {
	if m != nil {
		return m.CkToLastUpdateMemo
	}
	return nil
}

func (m *KeyMap) GetCcaToCk() []ConsAddrToKey {
	if m != nil {
		return m.CcaToCk
	}
	return nil
}

func init() {
	proto.RegisterType((*LastUpdateMemo)(nil), "interchain_security.ccv.provider.v1.LastUpdateMemo")
	proto.RegisterType((*KeyToKey)(nil), "interchain_security.ccv.provider.v1.KeyToKey")
	proto.RegisterType((*KeyToLastUpdateMemo)(nil), "interchain_security.ccv.provider.v1.KeyToLastUpdateMemo")
	proto.RegisterType((*ConsAddrToKey)(nil), "interchain_security.ccv.provider.v1.ConsAddrToKey")
	proto.RegisterType((*KeyMap)(nil), "interchain_security.ccv.provider.v1.KeyMap")
}

func init() {
	proto.RegisterFile("interchain_security/ccv/provider/v1/keymap.proto", fileDescriptor_864a04a770548246)
}

var fileDescriptor_864a04a770548246 = []byte{
	// 512 bytes of a gzipped FileDescriptorProto
	0x1f, 0x8b, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, 0xff, 0x9c, 0x54, 0xc1, 0x6e, 0xd3, 0x40,
	0x10, 0x8d, 0xe3, 0x34, 0xa4, 0xdb, 0x52, 0x55, 0xa6, 0x42, 0x51, 0xa9, 0x4c, 0x14, 0x2e, 0x39,
	0xd0, 0x75, 0x93, 0x5e, 0xb8, 0xd2, 0x1e, 0x4d, 0xa4, 0xca, 0x0a, 0x17, 0x04, 0xb2, 0x9c, 0xf1,
	0x92, 0x9a, 0x8d, 0x3d, 0xab, 0xf5, 0xc6, 0xe0, 0xbf, 0xe0, 0x23, 0x38, 0xf1, 0x25, 0x3d, 0xf6,
	0xc8, 0x09, 0xa1, 0xe4, 0x07, 0xf8, 0x04, 0xb4, 0xeb, 0x84, 0x2a, 0x85, 0x83, 0xd5, 0xdb, 0x8e,
	0xfd, 0xe6, 0xbd, 0xa7, 0x37, 0xb3, 0x4b, 0xce, 0x92, 0x4c, 0x31, 0x09, 0xd7, 0x51, 0x92, 0x85,
	0x39, 0x83, 0x85, 0x4c, 0x54, 0xe9, 0x01, 0x14, 0x9e, 0x90, 0x58, 0x24, 0x31, 0x93, 0x5e, 0x31,
	0xf4, 0x38, 0x2b, 0xd3, 0x48, 0x50, 0x21, 0x51, 0xa1, 0xf3, 0xe2, 0x3f, 0x1d, 0x14, 0xa0, 0xa0,
	0x9b, 0x0e, 0x5a, 0x0c, 0x8f, 0x8f, 0x66, 0x38, 0x43, 0x83, 0xf7, 0xf4, 0xa9, 0x6a, 0x3d, 0x3e,
	0x51, 0x2c, 0x8b, 0x99, 0x4c, 0x93, 0x4c, 0x79, 0x20, 0x4b, 0xa1, 0x50, 0x53, 0xe7, 0xd5, 0xdf,
	0xfe, 0x77, 0x8b, 0x1c, 0xbc, 0x89, 0x72, 0xf5, 0x56, 0xc4, 0x91, 0x62, 0x63, 0x96, 0xa2, 0xf3,
	0x92, 0x34, 0x81, 0x77, 0xad, 0x9e, 0x35, 0xd8, 0x1b, 0x9d, 0xd0, 0xbb, 0x6e, 0x5a, 0x75, 0xd3,
	0xab, 0xc5, 0x74, 0x9e, 0x80, 0xcf, 0xca, 0xa0, 0x09, 0x5c, 0xa3, 0x05, 0xef, 0x36, 0xeb, 0xa0,
	0x05, 0x77, 0x0e, 0x89, 0x0d, 0x10, 0x75, 0xed, 0x9e, 0x35, 0xd8, 0x0f, 0xf4, 0xd1, 0x39, 0x22,
	0x3b, 0x45, 0x0e, 0x49, 0xdc, 0x6d, 0xf5, 0xac, 0x41, 0x2b, 0xa8, 0x0a, 0xfd, 0x55, 0xe0, 0x67,
	0x26, 0xbb, 0x3b, 0x3d, 0x6b, 0x60, 0x07, 0x55, 0xd1, 0xff, 0x44, 0x3a, 0x3e, 0x2b, 0x27, 0xe8,
	0xb3, 0xd2, 0x39, 0x23, 0xad, 0x8f, 0x12, 0xd3, 0x5a, 0x3e, 0x0d, 0x52, 0x3b, 0x55, 0x58, 0xcf,
	0xa9, 0xc2, 0xfe, 0x37, 0x8b, 0x3c, 0x31, 0x62, 0xf7, 0xd2, 0xa1, 0xc4, 0xe6, 0xac, 0xac, 0x25,
	0xab, 0x81, 0xce, 0x07, 0x72, 0x38, 0x8f, 0x72, 0x15, 0x2e, 0x0c, 0x45, 0x98, 0xb2, 0x74, 0xe3,
	0xe1, 0x9c, 0xd6, 0x18, 0x2a, 0xdd, 0x96, 0x0f, 0x0e, 0xe6, 0x5b, 0x75, 0xff, 0x3d, 0x79, 0x7c,
	0x89, 0x59, 0xfe, 0x3a, 0x8e, 0x65, 0x95, 0xcb, 0x33, 0xb2, 0x0b, 0x98, 0xe5, 0x61, 0x14, 0xc7,
	0xd2, 0xb8, 0xdc, 0x0f, 0x3a, 0xb0, 0x46, 0x6c, 0xcc, 0x37, 0x6b, 0x9a, 0xef, 0xff, 0x6e, 0x92,
	0xb6, 0xcf, 0xca, 0x71, 0x24, 0x9c, 0x31, 0xe9, 0x08, 0x1e, 0x2a, 0x0c, 0xcd, 0x6e, 0xd8, 0x83,
	0xbd, 0xd1, 0x69, 0x2d, 0xff, 0x9b, 0x81, 0x5d, 0xb4, 0x6e, 0x7e, 0x3e, 0x6f, 0x04, 0x6d, 0xc1,
	0x27, 0x78, 0xc9, 0x35, 0x1d, 0x18, 0x3a, 0xb3, 0x3c, 0x0f, 0xa7, 0x03, 0x3e, 0xc1, 0x2b, 0xee,
	0x48, 0xf2, 0xb4, 0xa2, 0xfb, 0x27, 0x6b, 0xdb, 0x90, 0xbf, 0xaa, 0x4f, 0xbe, 0x1d, 0xf8, 0x5a,
	0xc7, 0xd1, 0x3a, 0xf7, 0x36, 0x61, 0x42, 0x76, 0x01, 0xa2, 0x75, 0x24, 0x2d, 0x23, 0x33, 0xaa,
	0x25, 0xb3, 0x35, 0xb0, 0xb5, 0xc0, 0x23, 0x80, 0x48, 0x07, 0x73, 0xe1, 0xdf, 0x2c, 0x5d, 0xeb,
	0x76, 0xe9, 0x5a, 0xbf, 0x96, 0xae, 0xf5, 0x75, 0xe5, 0x36, 0x6e, 0x57, 0x6e, 0xe3, 0xc7, 0xca,
	0x6d, 0xbc, 0x1b, 0xce, 0x12, 0x75, 0xbd, 0x98, 0x52, 0xc0, 0xd4, 0x03, 0xcc, 0x53, 0xcc, 0xbd,
	0x3b, 0xb5, 0xd3, 0xbf, 0xef, 0xc8, 0x17, 0xf3, 0x92, 0xa8, 0x52, 0xb0, 0x7c, 0xda, 0x36, 0x97,
	0xfc, 0xfc, 0x4f, 0x00, 0x00, 0x00, 0xff, 0xff, 0x22, 0x18, 0x7e, 0xc8, 0x71, 0x04, 0x00, 0x00,
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
		i = encodeVarintKeymap(dAtA, i, uint64(m.Power))
		i--
		dAtA[i] = 0x28
	}
	if m.Vscid != 0 {
		i = encodeVarintKeymap(dAtA, i, uint64(m.Vscid))
		i--
		dAtA[i] = 0x20
	}
	if len(m.Cca) > 0 {
		i -= len(m.Cca)
		copy(dAtA[i:], m.Cca)
		i = encodeVarintKeymap(dAtA, i, uint64(len(m.Cca)))
		i--
		dAtA[i] = 0x1a
	}
	if m.Pk != nil {
		{
			size, err := m.Pk.MarshalToSizedBuffer(dAtA[:i])
			if err != nil {
				return 0, err
			}
			i -= size
			i = encodeVarintKeymap(dAtA, i, uint64(size))
		}
		i--
		dAtA[i] = 0x12
	}
	if m.Ck != nil {
		{
			size, err := m.Ck.MarshalToSizedBuffer(dAtA[:i])
			if err != nil {
				return 0, err
			}
			i -= size
			i = encodeVarintKeymap(dAtA, i, uint64(size))
		}
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
			i = encodeVarintKeymap(dAtA, i, uint64(size))
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
			i = encodeVarintKeymap(dAtA, i, uint64(size))
		}
		i--
		dAtA[i] = 0xa
	}
	return len(dAtA) - i, nil
}

func (m *KeyToLastUpdateMemo) Marshal() (dAtA []byte, err error) {
	size := m.Size()
	dAtA = make([]byte, size)
	n, err := m.MarshalToSizedBuffer(dAtA[:size])
	if err != nil {
		return nil, err
	}
	return dAtA[:n], nil
}

func (m *KeyToLastUpdateMemo) MarshalTo(dAtA []byte) (int, error) {
	size := m.Size()
	return m.MarshalToSizedBuffer(dAtA[:size])
}

func (m *KeyToLastUpdateMemo) MarshalToSizedBuffer(dAtA []byte) (int, error) {
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
			i = encodeVarintKeymap(dAtA, i, uint64(size))
		}
		i--
		dAtA[i] = 0x12
	}
	if m.Key != nil {
		{
			size, err := m.Key.MarshalToSizedBuffer(dAtA[:i])
			if err != nil {
				return 0, err
			}
			i -= size
			i = encodeVarintKeymap(dAtA, i, uint64(size))
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
			i = encodeVarintKeymap(dAtA, i, uint64(size))
		}
		i--
		dAtA[i] = 0x12
	}
	if len(m.ConsAddr) > 0 {
		i -= len(m.ConsAddr)
		copy(dAtA[i:], m.ConsAddr)
		i = encodeVarintKeymap(dAtA, i, uint64(len(m.ConsAddr)))
		i--
		dAtA[i] = 0xa
	}
	return len(dAtA) - i, nil
}

func (m *KeyMap) Marshal() (dAtA []byte, err error) {
	size := m.Size()
	dAtA = make([]byte, size)
	n, err := m.MarshalToSizedBuffer(dAtA[:size])
	if err != nil {
		return nil, err
	}
	return dAtA[:n], nil
}

func (m *KeyMap) MarshalTo(dAtA []byte) (int, error) {
	size := m.Size()
	return m.MarshalToSizedBuffer(dAtA[:size])
}

func (m *KeyMap) MarshalToSizedBuffer(dAtA []byte) (int, error) {
	i := len(dAtA)
	_ = i
	var l int
	_ = l
	if len(m.CcaToCk) > 0 {
		for iNdEx := len(m.CcaToCk) - 1; iNdEx >= 0; iNdEx-- {
			{
				size, err := m.CcaToCk[iNdEx].MarshalToSizedBuffer(dAtA[:i])
				if err != nil {
					return 0, err
				}
				i -= size
				i = encodeVarintKeymap(dAtA, i, uint64(size))
			}
			i--
			dAtA[i] = 0x22
		}
	}
	if len(m.CkToLastUpdateMemo) > 0 {
		for iNdEx := len(m.CkToLastUpdateMemo) - 1; iNdEx >= 0; iNdEx-- {
			{
				size, err := m.CkToLastUpdateMemo[iNdEx].MarshalToSizedBuffer(dAtA[:i])
				if err != nil {
					return 0, err
				}
				i -= size
				i = encodeVarintKeymap(dAtA, i, uint64(size))
			}
			i--
			dAtA[i] = 0x1a
		}
	}
	if len(m.CkToPk) > 0 {
		for iNdEx := len(m.CkToPk) - 1; iNdEx >= 0; iNdEx-- {
			{
				size, err := m.CkToPk[iNdEx].MarshalToSizedBuffer(dAtA[:i])
				if err != nil {
					return 0, err
				}
				i -= size
				i = encodeVarintKeymap(dAtA, i, uint64(size))
			}
			i--
			dAtA[i] = 0x12
		}
	}
	if len(m.PkToCk) > 0 {
		for iNdEx := len(m.PkToCk) - 1; iNdEx >= 0; iNdEx-- {
			{
				size, err := m.PkToCk[iNdEx].MarshalToSizedBuffer(dAtA[:i])
				if err != nil {
					return 0, err
				}
				i -= size
				i = encodeVarintKeymap(dAtA, i, uint64(size))
			}
			i--
			dAtA[i] = 0xa
		}
	}
	return len(dAtA) - i, nil
}

func encodeVarintKeymap(dAtA []byte, offset int, v uint64) int {
	offset -= sovKeymap(v)
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
	if m.Ck != nil {
		l = m.Ck.Size()
		n += 1 + l + sovKeymap(uint64(l))
	}
	if m.Pk != nil {
		l = m.Pk.Size()
		n += 1 + l + sovKeymap(uint64(l))
	}
	l = len(m.Cca)
	if l > 0 {
		n += 1 + l + sovKeymap(uint64(l))
	}
	if m.Vscid != 0 {
		n += 1 + sovKeymap(uint64(m.Vscid))
	}
	if m.Power != 0 {
		n += 1 + sovKeymap(uint64(m.Power))
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
		n += 1 + l + sovKeymap(uint64(l))
	}
	if m.To != nil {
		l = m.To.Size()
		n += 1 + l + sovKeymap(uint64(l))
	}
	return n
}

func (m *KeyToLastUpdateMemo) Size() (n int) {
	if m == nil {
		return 0
	}
	var l int
	_ = l
	if m.Key != nil {
		l = m.Key.Size()
		n += 1 + l + sovKeymap(uint64(l))
	}
	if m.LastUpdateMemo != nil {
		l = m.LastUpdateMemo.Size()
		n += 1 + l + sovKeymap(uint64(l))
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
		n += 1 + l + sovKeymap(uint64(l))
	}
	if m.Key != nil {
		l = m.Key.Size()
		n += 1 + l + sovKeymap(uint64(l))
	}
	return n
}

func (m *KeyMap) Size() (n int) {
	if m == nil {
		return 0
	}
	var l int
	_ = l
	if len(m.PkToCk) > 0 {
		for _, e := range m.PkToCk {
			l = e.Size()
			n += 1 + l + sovKeymap(uint64(l))
		}
	}
	if len(m.CkToPk) > 0 {
		for _, e := range m.CkToPk {
			l = e.Size()
			n += 1 + l + sovKeymap(uint64(l))
		}
	}
	if len(m.CkToLastUpdateMemo) > 0 {
		for _, e := range m.CkToLastUpdateMemo {
			l = e.Size()
			n += 1 + l + sovKeymap(uint64(l))
		}
	}
	if len(m.CcaToCk) > 0 {
		for _, e := range m.CcaToCk {
			l = e.Size()
			n += 1 + l + sovKeymap(uint64(l))
		}
	}
	return n
}

func sovKeymap(x uint64) (n int) {
	return (math_bits.Len64(x|1) + 6) / 7
}
func sozKeymap(x uint64) (n int) {
	return sovKeymap(uint64((x << 1) ^ uint64((int64(x) >> 63))))
}
func (m *LastUpdateMemo) Unmarshal(dAtA []byte) error {
	l := len(dAtA)
	iNdEx := 0
	for iNdEx < l {
		preIndex := iNdEx
		var wire uint64
		for shift := uint(0); ; shift += 7 {
			if shift >= 64 {
				return ErrIntOverflowKeymap
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
				return fmt.Errorf("proto: wrong wireType = %d for field Ck", wireType)
			}
			var msglen int
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowKeymap
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
				return ErrInvalidLengthKeymap
			}
			postIndex := iNdEx + msglen
			if postIndex < 0 {
				return ErrInvalidLengthKeymap
			}
			if postIndex > l {
				return io.ErrUnexpectedEOF
			}
			if m.Ck == nil {
				m.Ck = &crypto.PublicKey{}
			}
			if err := m.Ck.Unmarshal(dAtA[iNdEx:postIndex]); err != nil {
				return err
			}
			iNdEx = postIndex
		case 2:
			if wireType != 2 {
				return fmt.Errorf("proto: wrong wireType = %d for field Pk", wireType)
			}
			var msglen int
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowKeymap
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
				return ErrInvalidLengthKeymap
			}
			postIndex := iNdEx + msglen
			if postIndex < 0 {
				return ErrInvalidLengthKeymap
			}
			if postIndex > l {
				return io.ErrUnexpectedEOF
			}
			if m.Pk == nil {
				m.Pk = &crypto.PublicKey{}
			}
			if err := m.Pk.Unmarshal(dAtA[iNdEx:postIndex]); err != nil {
				return err
			}
			iNdEx = postIndex
		case 3:
			if wireType != 2 {
				return fmt.Errorf("proto: wrong wireType = %d for field Cca", wireType)
			}
			var byteLen int
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowKeymap
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
				return ErrInvalidLengthKeymap
			}
			postIndex := iNdEx + byteLen
			if postIndex < 0 {
				return ErrInvalidLengthKeymap
			}
			if postIndex > l {
				return io.ErrUnexpectedEOF
			}
			m.Cca = append(m.Cca[:0], dAtA[iNdEx:postIndex]...)
			if m.Cca == nil {
				m.Cca = []byte{}
			}
			iNdEx = postIndex
		case 4:
			if wireType != 0 {
				return fmt.Errorf("proto: wrong wireType = %d for field Vscid", wireType)
			}
			m.Vscid = 0
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowKeymap
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
					return ErrIntOverflowKeymap
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
			skippy, err := skipKeymap(dAtA[iNdEx:])
			if err != nil {
				return err
			}
			if (skippy < 0) || (iNdEx+skippy) < 0 {
				return ErrInvalidLengthKeymap
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
				return ErrIntOverflowKeymap
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
					return ErrIntOverflowKeymap
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
				return ErrInvalidLengthKeymap
			}
			postIndex := iNdEx + msglen
			if postIndex < 0 {
				return ErrInvalidLengthKeymap
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
					return ErrIntOverflowKeymap
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
				return ErrInvalidLengthKeymap
			}
			postIndex := iNdEx + msglen
			if postIndex < 0 {
				return ErrInvalidLengthKeymap
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
			skippy, err := skipKeymap(dAtA[iNdEx:])
			if err != nil {
				return err
			}
			if (skippy < 0) || (iNdEx+skippy) < 0 {
				return ErrInvalidLengthKeymap
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
func (m *KeyToLastUpdateMemo) Unmarshal(dAtA []byte) error {
	l := len(dAtA)
	iNdEx := 0
	for iNdEx < l {
		preIndex := iNdEx
		var wire uint64
		for shift := uint(0); ; shift += 7 {
			if shift >= 64 {
				return ErrIntOverflowKeymap
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
			return fmt.Errorf("proto: KeyToLastUpdateMemo: wiretype end group for non-group")
		}
		if fieldNum <= 0 {
			return fmt.Errorf("proto: KeyToLastUpdateMemo: illegal tag %d (wire type %d)", fieldNum, wire)
		}
		switch fieldNum {
		case 1:
			if wireType != 2 {
				return fmt.Errorf("proto: wrong wireType = %d for field Key", wireType)
			}
			var msglen int
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowKeymap
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
				return ErrInvalidLengthKeymap
			}
			postIndex := iNdEx + msglen
			if postIndex < 0 {
				return ErrInvalidLengthKeymap
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
		case 2:
			if wireType != 2 {
				return fmt.Errorf("proto: wrong wireType = %d for field LastUpdateMemo", wireType)
			}
			var msglen int
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowKeymap
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
				return ErrInvalidLengthKeymap
			}
			postIndex := iNdEx + msglen
			if postIndex < 0 {
				return ErrInvalidLengthKeymap
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
			skippy, err := skipKeymap(dAtA[iNdEx:])
			if err != nil {
				return err
			}
			if (skippy < 0) || (iNdEx+skippy) < 0 {
				return ErrInvalidLengthKeymap
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
				return ErrIntOverflowKeymap
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
					return ErrIntOverflowKeymap
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
				return ErrInvalidLengthKeymap
			}
			postIndex := iNdEx + byteLen
			if postIndex < 0 {
				return ErrInvalidLengthKeymap
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
					return ErrIntOverflowKeymap
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
				return ErrInvalidLengthKeymap
			}
			postIndex := iNdEx + msglen
			if postIndex < 0 {
				return ErrInvalidLengthKeymap
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
			skippy, err := skipKeymap(dAtA[iNdEx:])
			if err != nil {
				return err
			}
			if (skippy < 0) || (iNdEx+skippy) < 0 {
				return ErrInvalidLengthKeymap
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
func (m *KeyMap) Unmarshal(dAtA []byte) error {
	l := len(dAtA)
	iNdEx := 0
	for iNdEx < l {
		preIndex := iNdEx
		var wire uint64
		for shift := uint(0); ; shift += 7 {
			if shift >= 64 {
				return ErrIntOverflowKeymap
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
			return fmt.Errorf("proto: KeyMap: wiretype end group for non-group")
		}
		if fieldNum <= 0 {
			return fmt.Errorf("proto: KeyMap: illegal tag %d (wire type %d)", fieldNum, wire)
		}
		switch fieldNum {
		case 1:
			if wireType != 2 {
				return fmt.Errorf("proto: wrong wireType = %d for field PkToCk", wireType)
			}
			var msglen int
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowKeymap
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
				return ErrInvalidLengthKeymap
			}
			postIndex := iNdEx + msglen
			if postIndex < 0 {
				return ErrInvalidLengthKeymap
			}
			if postIndex > l {
				return io.ErrUnexpectedEOF
			}
			m.PkToCk = append(m.PkToCk, KeyToKey{})
			if err := m.PkToCk[len(m.PkToCk)-1].Unmarshal(dAtA[iNdEx:postIndex]); err != nil {
				return err
			}
			iNdEx = postIndex
		case 2:
			if wireType != 2 {
				return fmt.Errorf("proto: wrong wireType = %d for field CkToPk", wireType)
			}
			var msglen int
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowKeymap
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
				return ErrInvalidLengthKeymap
			}
			postIndex := iNdEx + msglen
			if postIndex < 0 {
				return ErrInvalidLengthKeymap
			}
			if postIndex > l {
				return io.ErrUnexpectedEOF
			}
			m.CkToPk = append(m.CkToPk, KeyToKey{})
			if err := m.CkToPk[len(m.CkToPk)-1].Unmarshal(dAtA[iNdEx:postIndex]); err != nil {
				return err
			}
			iNdEx = postIndex
		case 3:
			if wireType != 2 {
				return fmt.Errorf("proto: wrong wireType = %d for field CkToLastUpdateMemo", wireType)
			}
			var msglen int
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowKeymap
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
				return ErrInvalidLengthKeymap
			}
			postIndex := iNdEx + msglen
			if postIndex < 0 {
				return ErrInvalidLengthKeymap
			}
			if postIndex > l {
				return io.ErrUnexpectedEOF
			}
			m.CkToLastUpdateMemo = append(m.CkToLastUpdateMemo, KeyToLastUpdateMemo{})
			if err := m.CkToLastUpdateMemo[len(m.CkToLastUpdateMemo)-1].Unmarshal(dAtA[iNdEx:postIndex]); err != nil {
				return err
			}
			iNdEx = postIndex
		case 4:
			if wireType != 2 {
				return fmt.Errorf("proto: wrong wireType = %d for field CcaToCk", wireType)
			}
			var msglen int
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowKeymap
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
				return ErrInvalidLengthKeymap
			}
			postIndex := iNdEx + msglen
			if postIndex < 0 {
				return ErrInvalidLengthKeymap
			}
			if postIndex > l {
				return io.ErrUnexpectedEOF
			}
			m.CcaToCk = append(m.CcaToCk, ConsAddrToKey{})
			if err := m.CcaToCk[len(m.CcaToCk)-1].Unmarshal(dAtA[iNdEx:postIndex]); err != nil {
				return err
			}
			iNdEx = postIndex
		default:
			iNdEx = preIndex
			skippy, err := skipKeymap(dAtA[iNdEx:])
			if err != nil {
				return err
			}
			if (skippy < 0) || (iNdEx+skippy) < 0 {
				return ErrInvalidLengthKeymap
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
func skipKeymap(dAtA []byte) (n int, err error) {
	l := len(dAtA)
	iNdEx := 0
	depth := 0
	for iNdEx < l {
		var wire uint64
		for shift := uint(0); ; shift += 7 {
			if shift >= 64 {
				return 0, ErrIntOverflowKeymap
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
					return 0, ErrIntOverflowKeymap
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
					return 0, ErrIntOverflowKeymap
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
				return 0, ErrInvalidLengthKeymap
			}
			iNdEx += length
		case 3:
			depth++
		case 4:
			if depth == 0 {
				return 0, ErrUnexpectedEndOfGroupKeymap
			}
			depth--
		case 5:
			iNdEx += 4
		default:
			return 0, fmt.Errorf("proto: illegal wireType %d", wireType)
		}
		if iNdEx < 0 {
			return 0, ErrInvalidLengthKeymap
		}
		if depth == 0 {
			return iNdEx, nil
		}
	}
	return 0, io.ErrUnexpectedEOF
}

var (
	ErrInvalidLengthKeymap        = fmt.Errorf("proto: negative length found during unmarshaling")
	ErrIntOverflowKeymap          = fmt.Errorf("proto: integer overflow")
	ErrUnexpectedEndOfGroupKeymap = fmt.Errorf("proto: unexpected end of group")
)
