// Code generated by protoc-gen-gogo. DO NOT EDIT.
// source: interchain_security/ccv/provider/v1/tx.proto

package types

import (
	context "context"
	fmt "fmt"
	types "github.com/cosmos/cosmos-sdk/codec/types"
	_ "github.com/cosmos/interchain-security/x/ccv/types"
	_ "github.com/gogo/protobuf/gogoproto"
	grpc1 "github.com/gogo/protobuf/grpc"
	proto "github.com/gogo/protobuf/proto"
	_ "github.com/regen-network/cosmos-proto"
	_ "google.golang.org/genproto/googleapis/api/annotations"
	grpc "google.golang.org/grpc"
	codes "google.golang.org/grpc/codes"
	status "google.golang.org/grpc/status"
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

type MsgDesignateConsensusKeyForConsumerChain struct {
	ChainId                  string     `protobuf:"bytes,1,opt,name=chain_id,json=chainId,proto3" json:"chain_id,omitempty"`
	ProviderValidatorAddress string     `protobuf:"bytes,2,opt,name=provider_validator_address,json=providerValidatorAddress,proto3" json:"provider_validator_address,omitempty" yaml:"address"`
	ConsumerValidatorPubkey  *types.Any `protobuf:"bytes,3,opt,name=consumer_validator_pubkey,json=consumerValidatorPubkey,proto3" json:"consumer_validator_pubkey,omitempty"`
}

func (m *MsgDesignateConsensusKeyForConsumerChain) Reset() {
	*m = MsgDesignateConsensusKeyForConsumerChain{}
}
func (m *MsgDesignateConsensusKeyForConsumerChain) String() string { return proto.CompactTextString(m) }
func (*MsgDesignateConsensusKeyForConsumerChain) ProtoMessage()    {}
func (*MsgDesignateConsensusKeyForConsumerChain) Descriptor() ([]byte, []int) {
	return fileDescriptor_43221a4391e9fbf4, []int{0}
}
func (m *MsgDesignateConsensusKeyForConsumerChain) XXX_Unmarshal(b []byte) error {
	return m.Unmarshal(b)
}
func (m *MsgDesignateConsensusKeyForConsumerChain) XXX_Marshal(b []byte, deterministic bool) ([]byte, error) {
	if deterministic {
		return xxx_messageInfo_MsgDesignateConsensusKeyForConsumerChain.Marshal(b, m, deterministic)
	} else {
		b = b[:cap(b)]
		n, err := m.MarshalToSizedBuffer(b)
		if err != nil {
			return nil, err
		}
		return b[:n], nil
	}
}
func (m *MsgDesignateConsensusKeyForConsumerChain) XXX_Merge(src proto.Message) {
	xxx_messageInfo_MsgDesignateConsensusKeyForConsumerChain.Merge(m, src)
}
func (m *MsgDesignateConsensusKeyForConsumerChain) XXX_Size() int {
	return m.Size()
}
func (m *MsgDesignateConsensusKeyForConsumerChain) XXX_DiscardUnknown() {
	xxx_messageInfo_MsgDesignateConsensusKeyForConsumerChain.DiscardUnknown(m)
}

var xxx_messageInfo_MsgDesignateConsensusKeyForConsumerChain proto.InternalMessageInfo

type MsgDesignateConsensusKeyForConsumerChainResponse struct {
	Placeholder string `protobuf:"bytes,1,opt,name=placeholder,proto3" json:"placeholder,omitempty"`
}

func (m *MsgDesignateConsensusKeyForConsumerChainResponse) Reset() {
	*m = MsgDesignateConsensusKeyForConsumerChainResponse{}
}
func (m *MsgDesignateConsensusKeyForConsumerChainResponse) String() string {
	return proto.CompactTextString(m)
}
func (*MsgDesignateConsensusKeyForConsumerChainResponse) ProtoMessage() {}
func (*MsgDesignateConsensusKeyForConsumerChainResponse) Descriptor() ([]byte, []int) {
	return fileDescriptor_43221a4391e9fbf4, []int{1}
}
func (m *MsgDesignateConsensusKeyForConsumerChainResponse) XXX_Unmarshal(b []byte) error {
	return m.Unmarshal(b)
}
func (m *MsgDesignateConsensusKeyForConsumerChainResponse) XXX_Marshal(b []byte, deterministic bool) ([]byte, error) {
	if deterministic {
		return xxx_messageInfo_MsgDesignateConsensusKeyForConsumerChainResponse.Marshal(b, m, deterministic)
	} else {
		b = b[:cap(b)]
		n, err := m.MarshalToSizedBuffer(b)
		if err != nil {
			return nil, err
		}
		return b[:n], nil
	}
}
func (m *MsgDesignateConsensusKeyForConsumerChainResponse) XXX_Merge(src proto.Message) {
	xxx_messageInfo_MsgDesignateConsensusKeyForConsumerChainResponse.Merge(m, src)
}
func (m *MsgDesignateConsensusKeyForConsumerChainResponse) XXX_Size() int {
	return m.Size()
}
func (m *MsgDesignateConsensusKeyForConsumerChainResponse) XXX_DiscardUnknown() {
	xxx_messageInfo_MsgDesignateConsensusKeyForConsumerChainResponse.DiscardUnknown(m)
}

var xxx_messageInfo_MsgDesignateConsensusKeyForConsumerChainResponse proto.InternalMessageInfo

func (m *MsgDesignateConsensusKeyForConsumerChainResponse) GetPlaceholder() string {
	if m != nil {
		return m.Placeholder
	}
	return ""
}

func init() {
	proto.RegisterType((*MsgDesignateConsensusKeyForConsumerChain)(nil), "interchain_security.ccv.provider.v1.MsgDesignateConsensusKeyForConsumerChain")
	proto.RegisterType((*MsgDesignateConsensusKeyForConsumerChainResponse)(nil), "interchain_security.ccv.provider.v1.MsgDesignateConsensusKeyForConsumerChainResponse")
}

func init() {
	proto.RegisterFile("interchain_security/ccv/provider/v1/tx.proto", fileDescriptor_43221a4391e9fbf4)
}

var fileDescriptor_43221a4391e9fbf4 = []byte{
	// 463 bytes of a gzipped FileDescriptorProto
	0x1f, 0x8b, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, 0xff, 0xac, 0x52, 0x4d, 0x6b, 0x13, 0x41,
	0x18, 0xde, 0x6d, 0x41, 0xeb, 0x16, 0x3c, 0x2c, 0x01, 0x37, 0x41, 0x36, 0x21, 0x22, 0xe4, 0x60,
	0x67, 0xda, 0x7a, 0xcb, 0xad, 0xa9, 0x08, 0x52, 0x02, 0x21, 0x54, 0x0f, 0x5e, 0xc2, 0xec, 0xec,
	0xb8, 0x19, 0xbb, 0x3b, 0xef, 0x30, 0x33, 0xbb, 0x74, 0xfe, 0x81, 0x17, 0xc1, 0x9f, 0xd0, 0x1f,
	0xe1, 0x8f, 0x10, 0x41, 0xe8, 0x45, 0xf0, 0x24, 0x92, 0x5c, 0x3c, 0xfb, 0x0b, 0x64, 0xbf, 0x6a,
	0x05, 0x0f, 0x7b, 0xf0, 0x36, 0xef, 0x3c, 0xef, 0xfb, 0xcc, 0xf3, 0xbc, 0xf3, 0x78, 0x4f, 0xb8,
	0x30, 0x4c, 0xd1, 0x35, 0xe1, 0x62, 0xa5, 0x19, 0xcd, 0x15, 0x37, 0x16, 0x53, 0x5a, 0x60, 0xa9,
	0xa0, 0xe0, 0x31, 0x53, 0xb8, 0x38, 0xc2, 0xe6, 0x12, 0x49, 0x05, 0x06, 0xfc, 0x47, 0xff, 0xe8,
	0x46, 0x94, 0x16, 0xa8, 0xed, 0x46, 0xc5, 0xd1, 0xe0, 0x61, 0x02, 0x90, 0xa4, 0x0c, 0x13, 0xc9,
	0x31, 0x11, 0x02, 0x0c, 0x31, 0x1c, 0x84, 0xae, 0x29, 0x06, 0xbd, 0x04, 0x12, 0xa8, 0x8e, 0xb8,
	0x3c, 0x35, 0xb7, 0x87, 0x5d, 0x64, 0x5c, 0x30, 0x9b, 0x11, 0xd9, 0x4c, 0xf4, 0x29, 0xe8, 0x0c,
	0xf4, 0xaa, 0xa6, 0xaa, 0x8b, 0x16, 0x6a, 0x04, 0x54, 0x55, 0x94, 0xbf, 0xc1, 0x44, 0xd8, 0x1a,
	0x1a, 0xbf, 0xdf, 0xf1, 0x26, 0x73, 0x9d, 0x3c, 0x63, 0x9a, 0x27, 0x82, 0x18, 0x76, 0x0a, 0x42,
	0x33, 0xa1, 0x73, 0x7d, 0xc6, 0xec, 0x73, 0x50, 0x65, 0x99, 0x67, 0x4c, 0x9d, 0x96, 0x42, 0xfc,
	0xbe, 0xb7, 0x57, 0x2b, 0xe2, 0x71, 0xe0, 0x8e, 0xdc, 0xc9, 0xbd, 0xe5, 0xdd, 0xaa, 0x7e, 0x11,
	0xfb, 0x0b, 0x6f, 0xd0, 0x2a, 0x5b, 0x15, 0x24, 0xe5, 0x31, 0x31, 0xa0, 0x56, 0x24, 0x8e, 0x15,
	0xd3, 0x3a, 0xd8, 0x29, 0x9b, 0x67, 0xfe, 0xaf, 0xef, 0xc3, 0xfb, 0x96, 0x64, 0xe9, 0x74, 0xdc,
	0x00, 0xe3, 0x65, 0xd0, 0x4e, 0xbd, 0x6a, 0x87, 0x4e, 0x6a, 0xc8, 0x7f, 0xeb, 0xf5, 0x69, 0xf3,
	0xfa, 0x2d, 0x46, 0x99, 0x47, 0x17, 0xcc, 0x06, 0xbb, 0x23, 0x77, 0xb2, 0x7f, 0xdc, 0x43, 0xb5,
	0x31, 0xd4, 0x1a, 0x43, 0x27, 0xc2, 0xce, 0x82, 0xcf, 0x1f, 0x0f, 0x7a, 0x8d, 0x7f, 0xaa, 0xac,
	0x34, 0x80, 0x16, 0x79, 0x74, 0xc6, 0xec, 0xf2, 0x41, 0x4b, 0x78, 0xf3, 0xd8, 0xa2, 0xa2, 0x9b,
	0xee, 0xbd, 0xbb, 0x1a, 0x3a, 0x3f, 0xaf, 0x86, 0xce, 0xf8, 0xdc, 0x3b, 0xec, 0xba, 0x8e, 0x25,
	0xd3, 0xb2, 0x84, 0xfd, 0x91, 0xb7, 0x2f, 0x53, 0x42, 0xd9, 0x1a, 0xd2, 0x98, 0xa9, 0x66, 0x33,
	0xb7, 0xaf, 0x8e, 0xbf, 0xba, 0xde, 0xee, 0x5c, 0x27, 0xfe, 0x17, 0xd7, 0x7b, 0xdc, 0x6d, 0xd5,
	0x73, 0xd4, 0x21, 0x59, 0xa8, 0xab, 0xd4, 0xc1, 0xcb, 0xff, 0x4a, 0xd7, 0x3a, 0x9f, 0x9d, 0x7f,
	0xda, 0x84, 0xee, 0xf5, 0x26, 0x74, 0x7f, 0x6c, 0x42, 0xf7, 0xc3, 0x36, 0x74, 0xae, 0xb7, 0xa1,
	0xf3, 0x6d, 0x1b, 0x3a, 0xaf, 0xa7, 0x09, 0x37, 0xeb, 0x3c, 0x42, 0x14, 0xb2, 0x26, 0x8b, 0xf8,
	0x8f, 0x82, 0x83, 0x9b, 0x44, 0x5f, 0xfe, 0x9d, 0x69, 0x63, 0x25, 0xd3, 0xd1, 0x9d, 0xea, 0x3b,
	0x9f, 0xfe, 0x0e, 0x00, 0x00, 0xff, 0xff, 0x61, 0x56, 0xb1, 0xa6, 0x8b, 0x03, 0x00, 0x00,
}

// Reference imports to suppress errors if they are not otherwise used.
var _ context.Context
var _ grpc.ClientConn

// This is a compile-time assertion to ensure that this generated file
// is compatible with the grpc package it is being compiled against.
const _ = grpc.SupportPackageIsVersion4

// MsgClient is the client API for Msg service.
//
// For semantics around ctx use and closing/ending streaming RPCs, please refer to https://godoc.org/google.golang.org/grpc#ClientConn.NewStream.
type MsgClient interface {
	DesignateConsensusKeyForConsumerChain(ctx context.Context, in *MsgDesignateConsensusKeyForConsumerChain, opts ...grpc.CallOption) (*MsgDesignateConsensusKeyForConsumerChainResponse, error)
}

type msgClient struct {
	cc grpc1.ClientConn
}

func NewMsgClient(cc grpc1.ClientConn) MsgClient {
	return &msgClient{cc}
}

func (c *msgClient) DesignateConsensusKeyForConsumerChain(ctx context.Context, in *MsgDesignateConsensusKeyForConsumerChain, opts ...grpc.CallOption) (*MsgDesignateConsensusKeyForConsumerChainResponse, error) {
	out := new(MsgDesignateConsensusKeyForConsumerChainResponse)
	err := c.cc.Invoke(ctx, "/interchain_security.ccv.provider.v1.Msg/DesignateConsensusKeyForConsumerChain", in, out, opts...)
	if err != nil {
		return nil, err
	}
	return out, nil
}

// MsgServer is the server API for Msg service.
type MsgServer interface {
	DesignateConsensusKeyForConsumerChain(context.Context, *MsgDesignateConsensusKeyForConsumerChain) (*MsgDesignateConsensusKeyForConsumerChainResponse, error)
}

// UnimplementedMsgServer can be embedded to have forward compatible implementations.
type UnimplementedMsgServer struct {
}

func (*UnimplementedMsgServer) DesignateConsensusKeyForConsumerChain(ctx context.Context, req *MsgDesignateConsensusKeyForConsumerChain) (*MsgDesignateConsensusKeyForConsumerChainResponse, error) {
	return nil, status.Errorf(codes.Unimplemented, "method DesignateConsensusKeyForConsumerChain not implemented")
}

func RegisterMsgServer(s grpc1.Server, srv MsgServer) {
	s.RegisterService(&_Msg_serviceDesc, srv)
}

func _Msg_DesignateConsensusKeyForConsumerChain_Handler(srv interface{}, ctx context.Context, dec func(interface{}) error, interceptor grpc.UnaryServerInterceptor) (interface{}, error) {
	in := new(MsgDesignateConsensusKeyForConsumerChain)
	if err := dec(in); err != nil {
		return nil, err
	}
	if interceptor == nil {
		return srv.(MsgServer).DesignateConsensusKeyForConsumerChain(ctx, in)
	}
	info := &grpc.UnaryServerInfo{
		Server:     srv,
		FullMethod: "/interchain_security.ccv.provider.v1.Msg/DesignateConsensusKeyForConsumerChain",
	}
	handler := func(ctx context.Context, req interface{}) (interface{}, error) {
		return srv.(MsgServer).DesignateConsensusKeyForConsumerChain(ctx, req.(*MsgDesignateConsensusKeyForConsumerChain))
	}
	return interceptor(ctx, in, info, handler)
}

var _Msg_serviceDesc = grpc.ServiceDesc{
	ServiceName: "interchain_security.ccv.provider.v1.Msg",
	HandlerType: (*MsgServer)(nil),
	Methods: []grpc.MethodDesc{
		{
			MethodName: "DesignateConsensusKeyForConsumerChain",
			Handler:    _Msg_DesignateConsensusKeyForConsumerChain_Handler,
		},
	},
	Streams:  []grpc.StreamDesc{},
	Metadata: "interchain_security/ccv/provider/v1/tx.proto",
}

func (m *MsgDesignateConsensusKeyForConsumerChain) Marshal() (dAtA []byte, err error) {
	size := m.Size()
	dAtA = make([]byte, size)
	n, err := m.MarshalToSizedBuffer(dAtA[:size])
	if err != nil {
		return nil, err
	}
	return dAtA[:n], nil
}

func (m *MsgDesignateConsensusKeyForConsumerChain) MarshalTo(dAtA []byte) (int, error) {
	size := m.Size()
	return m.MarshalToSizedBuffer(dAtA[:size])
}

func (m *MsgDesignateConsensusKeyForConsumerChain) MarshalToSizedBuffer(dAtA []byte) (int, error) {
	i := len(dAtA)
	_ = i
	var l int
	_ = l
	if m.ConsumerValidatorPubkey != nil {
		{
			size, err := m.ConsumerValidatorPubkey.MarshalToSizedBuffer(dAtA[:i])
			if err != nil {
				return 0, err
			}
			i -= size
			i = encodeVarintTx(dAtA, i, uint64(size))
		}
		i--
		dAtA[i] = 0x1a
	}
	if len(m.ProviderValidatorAddress) > 0 {
		i -= len(m.ProviderValidatorAddress)
		copy(dAtA[i:], m.ProviderValidatorAddress)
		i = encodeVarintTx(dAtA, i, uint64(len(m.ProviderValidatorAddress)))
		i--
		dAtA[i] = 0x12
	}
	if len(m.ChainId) > 0 {
		i -= len(m.ChainId)
		copy(dAtA[i:], m.ChainId)
		i = encodeVarintTx(dAtA, i, uint64(len(m.ChainId)))
		i--
		dAtA[i] = 0xa
	}
	return len(dAtA) - i, nil
}

func (m *MsgDesignateConsensusKeyForConsumerChainResponse) Marshal() (dAtA []byte, err error) {
	size := m.Size()
	dAtA = make([]byte, size)
	n, err := m.MarshalToSizedBuffer(dAtA[:size])
	if err != nil {
		return nil, err
	}
	return dAtA[:n], nil
}

func (m *MsgDesignateConsensusKeyForConsumerChainResponse) MarshalTo(dAtA []byte) (int, error) {
	size := m.Size()
	return m.MarshalToSizedBuffer(dAtA[:size])
}

func (m *MsgDesignateConsensusKeyForConsumerChainResponse) MarshalToSizedBuffer(dAtA []byte) (int, error) {
	i := len(dAtA)
	_ = i
	var l int
	_ = l
	if len(m.Placeholder) > 0 {
		i -= len(m.Placeholder)
		copy(dAtA[i:], m.Placeholder)
		i = encodeVarintTx(dAtA, i, uint64(len(m.Placeholder)))
		i--
		dAtA[i] = 0xa
	}
	return len(dAtA) - i, nil
}

func encodeVarintTx(dAtA []byte, offset int, v uint64) int {
	offset -= sovTx(v)
	base := offset
	for v >= 1<<7 {
		dAtA[offset] = uint8(v&0x7f | 0x80)
		v >>= 7
		offset++
	}
	dAtA[offset] = uint8(v)
	return base
}
func (m *MsgDesignateConsensusKeyForConsumerChain) Size() (n int) {
	if m == nil {
		return 0
	}
	var l int
	_ = l
	l = len(m.ChainId)
	if l > 0 {
		n += 1 + l + sovTx(uint64(l))
	}
	l = len(m.ProviderValidatorAddress)
	if l > 0 {
		n += 1 + l + sovTx(uint64(l))
	}
	if m.ConsumerValidatorPubkey != nil {
		l = m.ConsumerValidatorPubkey.Size()
		n += 1 + l + sovTx(uint64(l))
	}
	return n
}

func (m *MsgDesignateConsensusKeyForConsumerChainResponse) Size() (n int) {
	if m == nil {
		return 0
	}
	var l int
	_ = l
	l = len(m.Placeholder)
	if l > 0 {
		n += 1 + l + sovTx(uint64(l))
	}
	return n
}

func sovTx(x uint64) (n int) {
	return (math_bits.Len64(x|1) + 6) / 7
}
func sozTx(x uint64) (n int) {
	return sovTx(uint64((x << 1) ^ uint64((int64(x) >> 63))))
}
func (m *MsgDesignateConsensusKeyForConsumerChain) Unmarshal(dAtA []byte) error {
	l := len(dAtA)
	iNdEx := 0
	for iNdEx < l {
		preIndex := iNdEx
		var wire uint64
		for shift := uint(0); ; shift += 7 {
			if shift >= 64 {
				return ErrIntOverflowTx
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
			return fmt.Errorf("proto: MsgDesignateConsensusKeyForConsumerChain: wiretype end group for non-group")
		}
		if fieldNum <= 0 {
			return fmt.Errorf("proto: MsgDesignateConsensusKeyForConsumerChain: illegal tag %d (wire type %d)", fieldNum, wire)
		}
		switch fieldNum {
		case 1:
			if wireType != 2 {
				return fmt.Errorf("proto: wrong wireType = %d for field ChainId", wireType)
			}
			var stringLen uint64
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowTx
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
				return ErrInvalidLengthTx
			}
			postIndex := iNdEx + intStringLen
			if postIndex < 0 {
				return ErrInvalidLengthTx
			}
			if postIndex > l {
				return io.ErrUnexpectedEOF
			}
			m.ChainId = string(dAtA[iNdEx:postIndex])
			iNdEx = postIndex
		case 2:
			if wireType != 2 {
				return fmt.Errorf("proto: wrong wireType = %d for field ProviderValidatorAddress", wireType)
			}
			var stringLen uint64
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowTx
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
				return ErrInvalidLengthTx
			}
			postIndex := iNdEx + intStringLen
			if postIndex < 0 {
				return ErrInvalidLengthTx
			}
			if postIndex > l {
				return io.ErrUnexpectedEOF
			}
			m.ProviderValidatorAddress = string(dAtA[iNdEx:postIndex])
			iNdEx = postIndex
		case 3:
			if wireType != 2 {
				return fmt.Errorf("proto: wrong wireType = %d for field ConsumerValidatorPubkey", wireType)
			}
			var msglen int
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowTx
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
				return ErrInvalidLengthTx
			}
			postIndex := iNdEx + msglen
			if postIndex < 0 {
				return ErrInvalidLengthTx
			}
			if postIndex > l {
				return io.ErrUnexpectedEOF
			}
			if m.ConsumerValidatorPubkey == nil {
				m.ConsumerValidatorPubkey = &types.Any{}
			}
			if err := m.ConsumerValidatorPubkey.Unmarshal(dAtA[iNdEx:postIndex]); err != nil {
				return err
			}
			iNdEx = postIndex
		default:
			iNdEx = preIndex
			skippy, err := skipTx(dAtA[iNdEx:])
			if err != nil {
				return err
			}
			if (skippy < 0) || (iNdEx+skippy) < 0 {
				return ErrInvalidLengthTx
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
func (m *MsgDesignateConsensusKeyForConsumerChainResponse) Unmarshal(dAtA []byte) error {
	l := len(dAtA)
	iNdEx := 0
	for iNdEx < l {
		preIndex := iNdEx
		var wire uint64
		for shift := uint(0); ; shift += 7 {
			if shift >= 64 {
				return ErrIntOverflowTx
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
			return fmt.Errorf("proto: MsgDesignateConsensusKeyForConsumerChainResponse: wiretype end group for non-group")
		}
		if fieldNum <= 0 {
			return fmt.Errorf("proto: MsgDesignateConsensusKeyForConsumerChainResponse: illegal tag %d (wire type %d)", fieldNum, wire)
		}
		switch fieldNum {
		case 1:
			if wireType != 2 {
				return fmt.Errorf("proto: wrong wireType = %d for field Placeholder", wireType)
			}
			var stringLen uint64
			for shift := uint(0); ; shift += 7 {
				if shift >= 64 {
					return ErrIntOverflowTx
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
				return ErrInvalidLengthTx
			}
			postIndex := iNdEx + intStringLen
			if postIndex < 0 {
				return ErrInvalidLengthTx
			}
			if postIndex > l {
				return io.ErrUnexpectedEOF
			}
			m.Placeholder = string(dAtA[iNdEx:postIndex])
			iNdEx = postIndex
		default:
			iNdEx = preIndex
			skippy, err := skipTx(dAtA[iNdEx:])
			if err != nil {
				return err
			}
			if (skippy < 0) || (iNdEx+skippy) < 0 {
				return ErrInvalidLengthTx
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
func skipTx(dAtA []byte) (n int, err error) {
	l := len(dAtA)
	iNdEx := 0
	depth := 0
	for iNdEx < l {
		var wire uint64
		for shift := uint(0); ; shift += 7 {
			if shift >= 64 {
				return 0, ErrIntOverflowTx
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
					return 0, ErrIntOverflowTx
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
					return 0, ErrIntOverflowTx
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
				return 0, ErrInvalidLengthTx
			}
			iNdEx += length
		case 3:
			depth++
		case 4:
			if depth == 0 {
				return 0, ErrUnexpectedEndOfGroupTx
			}
			depth--
		case 5:
			iNdEx += 4
		default:
			return 0, fmt.Errorf("proto: illegal wireType %d", wireType)
		}
		if iNdEx < 0 {
			return 0, ErrInvalidLengthTx
		}
		if depth == 0 {
			return iNdEx, nil
		}
	}
	return 0, io.ErrUnexpectedEOF
}

var (
	ErrInvalidLengthTx        = fmt.Errorf("proto: negative length found during unmarshaling")
	ErrIntOverflowTx          = fmt.Errorf("proto: integer overflow")
	ErrUnexpectedEndOfGroupTx = fmt.Errorf("proto: unexpected end of group")
)
