// Code generated by protoc-gen-gogo. DO NOT EDIT.
// source: interchain_security/ccv/provider/v1/tx.proto

package types

import (
	context "context"
	fmt "fmt"
	_ "github.com/cosmos/cosmos-sdk/codec/types"
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

type MsgAssignConsumerKey struct {
	// The chain id of the consumer chain to assign a consensus public key to
	ChainId string `protobuf:"bytes,1,opt,name=chain_id,json=chainId,proto3" json:"chain_id,omitempty"`
	// The validator address on the provider
	ProviderAddr string `protobuf:"bytes,2,opt,name=provider_addr,json=providerAddr,proto3" json:"provider_addr,omitempty" yaml:"address"`
	// The consensus public key to use on the consumer.
	// in json string format corresponding to proto-any, ex:
	// `{"@type":"/cosmos.crypto.ed25519.PubKey","key":"Ui5Gf1+mtWUdH8u3xlmzdKID+F3PK0sfXZ73GZ6q6is="}`
	ConsumerKey string `protobuf:"bytes,3,opt,name=consumer_key,json=consumerKey,proto3" json:"consumer_key,omitempty"`
}

func (m *MsgAssignConsumerKey) Reset()         { *m = MsgAssignConsumerKey{} }
func (m *MsgAssignConsumerKey) String() string { return proto.CompactTextString(m) }
func (*MsgAssignConsumerKey) ProtoMessage()    {}
func (*MsgAssignConsumerKey) Descriptor() ([]byte, []int) {
	return fileDescriptor_43221a4391e9fbf4, []int{0}
}
func (m *MsgAssignConsumerKey) XXX_Unmarshal(b []byte) error {
	return m.Unmarshal(b)
}
func (m *MsgAssignConsumerKey) XXX_Marshal(b []byte, deterministic bool) ([]byte, error) {
	if deterministic {
		return xxx_messageInfo_MsgAssignConsumerKey.Marshal(b, m, deterministic)
	} else {
		b = b[:cap(b)]
		n, err := m.MarshalToSizedBuffer(b)
		if err != nil {
			return nil, err
		}
		return b[:n], nil
	}
}
func (m *MsgAssignConsumerKey) XXX_Merge(src proto.Message) {
	xxx_messageInfo_MsgAssignConsumerKey.Merge(m, src)
}
func (m *MsgAssignConsumerKey) XXX_Size() int {
	return m.Size()
}
func (m *MsgAssignConsumerKey) XXX_DiscardUnknown() {
	xxx_messageInfo_MsgAssignConsumerKey.DiscardUnknown(m)
}

var xxx_messageInfo_MsgAssignConsumerKey proto.InternalMessageInfo

type MsgAssignConsumerKeyResponse struct {
}

func (m *MsgAssignConsumerKeyResponse) Reset()         { *m = MsgAssignConsumerKeyResponse{} }
func (m *MsgAssignConsumerKeyResponse) String() string { return proto.CompactTextString(m) }
func (*MsgAssignConsumerKeyResponse) ProtoMessage()    {}
func (*MsgAssignConsumerKeyResponse) Descriptor() ([]byte, []int) {
	return fileDescriptor_43221a4391e9fbf4, []int{1}
}
func (m *MsgAssignConsumerKeyResponse) XXX_Unmarshal(b []byte) error {
	return m.Unmarshal(b)
}
func (m *MsgAssignConsumerKeyResponse) XXX_Marshal(b []byte, deterministic bool) ([]byte, error) {
	if deterministic {
		return xxx_messageInfo_MsgAssignConsumerKeyResponse.Marshal(b, m, deterministic)
	} else {
		b = b[:cap(b)]
		n, err := m.MarshalToSizedBuffer(b)
		if err != nil {
			return nil, err
		}
		return b[:n], nil
	}
}
func (m *MsgAssignConsumerKeyResponse) XXX_Merge(src proto.Message) {
	xxx_messageInfo_MsgAssignConsumerKeyResponse.Merge(m, src)
}
func (m *MsgAssignConsumerKeyResponse) XXX_Size() int {
	return m.Size()
}
func (m *MsgAssignConsumerKeyResponse) XXX_DiscardUnknown() {
	xxx_messageInfo_MsgAssignConsumerKeyResponse.DiscardUnknown(m)
}

var xxx_messageInfo_MsgAssignConsumerKeyResponse proto.InternalMessageInfo

func init() {
	proto.RegisterType((*MsgAssignConsumerKey)(nil), "interchain_security.ccv.provider.v1.MsgAssignConsumerKey")
	proto.RegisterType((*MsgAssignConsumerKeyResponse)(nil), "interchain_security.ccv.provider.v1.MsgAssignConsumerKeyResponse")
}

func init() {
	proto.RegisterFile("interchain_security/ccv/provider/v1/tx.proto", fileDescriptor_43221a4391e9fbf4)
}

var fileDescriptor_43221a4391e9fbf4 = []byte{
	// 375 bytes of a gzipped FileDescriptorProto
	0x1f, 0x8b, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, 0xff, 0x9c, 0x52, 0x3d, 0x4f, 0xeb, 0x30,
	0x14, 0x8d, 0x5f, 0xa5, 0xf7, 0xfa, 0xfc, 0xfa, 0x9e, 0xf4, 0xa2, 0x0e, 0x6d, 0x55, 0xa5, 0x10,
	0x16, 0x06, 0x88, 0xd5, 0x32, 0x20, 0x2a, 0x31, 0xb4, 0x4c, 0x08, 0x75, 0xe9, 0x82, 0xc4, 0x12,
	0xa5, 0x8e, 0x71, 0x2d, 0x1a, 0x3b, 0xb2, 0x9d, 0xa8, 0xf9, 0x07, 0x8c, 0x30, 0x21, 0xb6, 0xfe,
	0x1c, 0xc6, 0x8e, 0x4c, 0x08, 0xb5, 0x0b, 0x33, 0xbf, 0x00, 0x35, 0x1f, 0x54, 0x88, 0x0e, 0x88,
	0xed, 0xde, 0x7b, 0x8e, 0xcf, 0x39, 0xf2, 0xbd, 0x70, 0x8f, 0x71, 0x4d, 0x24, 0x1e, 0x7b, 0x8c,
	0xbb, 0x8a, 0xe0, 0x48, 0x32, 0x9d, 0x20, 0x8c, 0x63, 0x14, 0x4a, 0x11, 0x33, 0x9f, 0x48, 0x14,
	0xb7, 0x91, 0x9e, 0x3a, 0xa1, 0x14, 0x5a, 0x98, 0x3b, 0x1b, 0xd8, 0x0e, 0xc6, 0xb1, 0x53, 0xb0,
	0x9d, 0xb8, 0xdd, 0x68, 0x52, 0x21, 0xe8, 0x84, 0x20, 0x2f, 0x64, 0xc8, 0xe3, 0x5c, 0x68, 0x4f,
	0x33, 0xc1, 0x55, 0x26, 0xd1, 0xa8, 0x52, 0x41, 0x45, 0x5a, 0xa2, 0x55, 0x95, 0x4f, 0xeb, 0x58,
	0xa8, 0x40, 0x28, 0x37, 0x03, 0xb2, 0xa6, 0x80, 0x72, 0xb9, 0xb4, 0x1b, 0x45, 0x97, 0xc8, 0xe3,
	0x49, 0x06, 0xd9, 0x77, 0x00, 0x56, 0x07, 0x8a, 0xf6, 0x94, 0x62, 0x94, 0x9f, 0x08, 0xae, 0xa2,
	0x80, 0xc8, 0x33, 0x92, 0x98, 0x75, 0x58, 0xce, 0x42, 0x32, 0xbf, 0x06, 0xb6, 0xc0, 0xee, 0xef,
	0xe1, 0xaf, 0xb4, 0x3f, 0xf5, 0xcd, 0x43, 0xf8, 0xb7, 0x08, 0xeb, 0x7a, 0xbe, 0x2f, 0x6b, 0x3f,
	0x56, 0x78, 0xdf, 0x7c, 0x7d, 0x6a, 0xfd, 0x4b, 0xbc, 0x60, 0xd2, 0xb5, 0x57, 0x53, 0xa2, 0x94,
	0x3d, 0xac, 0x14, 0xc4, 0x9e, 0xef, 0x4b, 0x73, 0x1b, 0x56, 0x70, 0x6e, 0xe1, 0x5e, 0x91, 0xa4,
	0x56, 0x4a, 0x75, 0xff, 0xe0, 0xb5, 0x6d, 0xb7, 0x7c, 0x3d, 0x6b, 0x19, 0x2f, 0xb3, 0x96, 0x61,
	0x5b, 0xb0, 0xb9, 0x29, 0xd8, 0x90, 0xa8, 0x50, 0x70, 0x45, 0x3a, 0xf7, 0x00, 0x96, 0x06, 0x8a,
	0x9a, 0xb7, 0x00, 0xfe, 0xff, 0x1c, 0xff, 0xc8, 0xf9, 0xc2, 0x3f, 0x3b, 0x9b, 0x0c, 0x1a, 0xbd,
	0x6f, 0x3f, 0x2d, 0xb2, 0xf5, 0xcf, 0x1f, 0x16, 0x16, 0x98, 0x2f, 0x2c, 0xf0, 0xbc, 0xb0, 0xc0,
	0xcd, 0xd2, 0x32, 0xe6, 0x4b, 0xcb, 0x78, 0x5c, 0x5a, 0xc6, 0xc5, 0x31, 0x65, 0x7a, 0x1c, 0x8d,
	0x1c, 0x2c, 0x82, 0x7c, 0x47, 0x68, 0xed, 0xb6, 0xff, 0x7e, 0x3e, 0x71, 0x07, 0x4d, 0x3f, 0xde,
	0x90, 0x4e, 0x42, 0xa2, 0x46, 0x3f, 0xd3, 0xad, 0x1d, 0xbc, 0x05, 0x00, 0x00, 0xff, 0xff, 0x9a,
	0x29, 0xaf, 0xde, 0x74, 0x02, 0x00, 0x00,
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
	AssignConsumerKey(ctx context.Context, in *MsgAssignConsumerKey, opts ...grpc.CallOption) (*MsgAssignConsumerKeyResponse, error)
}

type msgClient struct {
	cc grpc1.ClientConn
}

func NewMsgClient(cc grpc1.ClientConn) MsgClient {
	return &msgClient{cc}
}

func (c *msgClient) AssignConsumerKey(ctx context.Context, in *MsgAssignConsumerKey, opts ...grpc.CallOption) (*MsgAssignConsumerKeyResponse, error) {
	out := new(MsgAssignConsumerKeyResponse)
	err := c.cc.Invoke(ctx, "/interchain_security.ccv.provider.v1.Msg/AssignConsumerKey", in, out, opts...)
	if err != nil {
		return nil, err
	}
	return out, nil
}

// MsgServer is the server API for Msg service.
type MsgServer interface {
	AssignConsumerKey(context.Context, *MsgAssignConsumerKey) (*MsgAssignConsumerKeyResponse, error)
}

// UnimplementedMsgServer can be embedded to have forward compatible implementations.
type UnimplementedMsgServer struct {
}

func (*UnimplementedMsgServer) AssignConsumerKey(ctx context.Context, req *MsgAssignConsumerKey) (*MsgAssignConsumerKeyResponse, error) {
	return nil, status.Errorf(codes.Unimplemented, "method AssignConsumerKey not implemented")
}

func RegisterMsgServer(s grpc1.Server, srv MsgServer) {
	s.RegisterService(&_Msg_serviceDesc, srv)
}

func _Msg_AssignConsumerKey_Handler(srv interface{}, ctx context.Context, dec func(interface{}) error, interceptor grpc.UnaryServerInterceptor) (interface{}, error) {
	in := new(MsgAssignConsumerKey)
	if err := dec(in); err != nil {
		return nil, err
	}
	if interceptor == nil {
		return srv.(MsgServer).AssignConsumerKey(ctx, in)
	}
	info := &grpc.UnaryServerInfo{
		Server:     srv,
		FullMethod: "/interchain_security.ccv.provider.v1.Msg/AssignConsumerKey",
	}
	handler := func(ctx context.Context, req interface{}) (interface{}, error) {
		return srv.(MsgServer).AssignConsumerKey(ctx, req.(*MsgAssignConsumerKey))
	}
	return interceptor(ctx, in, info, handler)
}

var _Msg_serviceDesc = grpc.ServiceDesc{
	ServiceName: "interchain_security.ccv.provider.v1.Msg",
	HandlerType: (*MsgServer)(nil),
	Methods: []grpc.MethodDesc{
		{
			MethodName: "AssignConsumerKey",
			Handler:    _Msg_AssignConsumerKey_Handler,
		},
	},
	Streams:  []grpc.StreamDesc{},
	Metadata: "interchain_security/ccv/provider/v1/tx.proto",
}

func (m *MsgAssignConsumerKey) Marshal() (dAtA []byte, err error) {
	size := m.Size()
	dAtA = make([]byte, size)
	n, err := m.MarshalToSizedBuffer(dAtA[:size])
	if err != nil {
		return nil, err
	}
	return dAtA[:n], nil
}

func (m *MsgAssignConsumerKey) MarshalTo(dAtA []byte) (int, error) {
	size := m.Size()
	return m.MarshalToSizedBuffer(dAtA[:size])
}

func (m *MsgAssignConsumerKey) MarshalToSizedBuffer(dAtA []byte) (int, error) {
	i := len(dAtA)
	_ = i
	var l int
	_ = l
	if len(m.ConsumerKey) > 0 {
		i -= len(m.ConsumerKey)
		copy(dAtA[i:], m.ConsumerKey)
		i = encodeVarintTx(dAtA, i, uint64(len(m.ConsumerKey)))
		i--
		dAtA[i] = 0x1a
	}
	if len(m.ProviderAddr) > 0 {
		i -= len(m.ProviderAddr)
		copy(dAtA[i:], m.ProviderAddr)
		i = encodeVarintTx(dAtA, i, uint64(len(m.ProviderAddr)))
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

func (m *MsgAssignConsumerKeyResponse) Marshal() (dAtA []byte, err error) {
	size := m.Size()
	dAtA = make([]byte, size)
	n, err := m.MarshalToSizedBuffer(dAtA[:size])
	if err != nil {
		return nil, err
	}
	return dAtA[:n], nil
}

func (m *MsgAssignConsumerKeyResponse) MarshalTo(dAtA []byte) (int, error) {
	size := m.Size()
	return m.MarshalToSizedBuffer(dAtA[:size])
}

func (m *MsgAssignConsumerKeyResponse) MarshalToSizedBuffer(dAtA []byte) (int, error) {
	i := len(dAtA)
	_ = i
	var l int
	_ = l
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
func (m *MsgAssignConsumerKey) Size() (n int) {
	if m == nil {
		return 0
	}
	var l int
	_ = l
	l = len(m.ChainId)
	if l > 0 {
		n += 1 + l + sovTx(uint64(l))
	}
	l = len(m.ProviderAddr)
	if l > 0 {
		n += 1 + l + sovTx(uint64(l))
	}
	l = len(m.ConsumerKey)
	if l > 0 {
		n += 1 + l + sovTx(uint64(l))
	}
	return n
}

func (m *MsgAssignConsumerKeyResponse) Size() (n int) {
	if m == nil {
		return 0
	}
	var l int
	_ = l
	return n
}

func sovTx(x uint64) (n int) {
	return (math_bits.Len64(x|1) + 6) / 7
}
func sozTx(x uint64) (n int) {
	return sovTx(uint64((x << 1) ^ uint64((int64(x) >> 63))))
}
func (m *MsgAssignConsumerKey) Unmarshal(dAtA []byte) error {
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
			return fmt.Errorf("proto: MsgAssignConsumerKey: wiretype end group for non-group")
		}
		if fieldNum <= 0 {
			return fmt.Errorf("proto: MsgAssignConsumerKey: illegal tag %d (wire type %d)", fieldNum, wire)
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
				return fmt.Errorf("proto: wrong wireType = %d for field ProviderAddr", wireType)
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
			m.ProviderAddr = string(dAtA[iNdEx:postIndex])
			iNdEx = postIndex
		case 3:
			if wireType != 2 {
				return fmt.Errorf("proto: wrong wireType = %d for field ConsumerKey", wireType)
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
			m.ConsumerKey = string(dAtA[iNdEx:postIndex])
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
func (m *MsgAssignConsumerKeyResponse) Unmarshal(dAtA []byte) error {
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
			return fmt.Errorf("proto: MsgAssignConsumerKeyResponse: wiretype end group for non-group")
		}
		if fieldNum <= 0 {
			return fmt.Errorf("proto: MsgAssignConsumerKeyResponse: illegal tag %d (wire type %d)", fieldNum, wire)
		}
		switch fieldNum {
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
