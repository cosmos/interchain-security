package core

import (
	codectypes "github.com/cosmos/cosmos-sdk/codec/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	proto "github.com/gogo/protobuf/proto"

	"github.com/cosmos/ibc-go/v3/modules/core/exported"
)

// TODO: Determine if needs to be deleted (was in informal/ibc-go for codec_test only)

// UnpackAcknowledgement unpacks an Any into an Acknowledgement. It returns an error if the
// Any can't be unpacked into an Acknowledgement.
func UnpackAcknowledgement(any *codectypes.Any) (exported.Acknowledgement, error) {
	if any == nil {
		return nil, sdkerrors.Wrap(sdkerrors.ErrUnpackAny, "protobuf Any message cannot be nil")
	}

	ack, ok := any.GetCachedValue().(exported.Acknowledgement)
	if !ok {
		return nil, sdkerrors.Wrapf(sdkerrors.ErrUnpackAny, "cannot unpack Any into Acknowledgement %T", any)
	}

	return ack, nil
}

// PackAcknowledgement constructs a new Any packed with the given acknowledgement value. It returns
// an error if the acknowledgement can't be casted to a protobuf message or if the concrete
// implemention is not registered to the protobuf codec.
func PackAcknowledgement(acknowledgement exported.Acknowledgement) (*codectypes.Any, error) {
	msg, ok := acknowledgement.(proto.Message)
	if !ok {
		return nil, sdkerrors.Wrapf(sdkerrors.ErrPackAny, "cannot proto marshal %T", acknowledgement)
	}

	anyAcknowledgement, err := codectypes.NewAnyWithValue(msg)
	if err != nil {
		return nil, sdkerrors.Wrap(sdkerrors.ErrPackAny, err.Error())
	}

	return anyAcknowledgement, nil
}
