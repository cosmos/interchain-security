package types

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
)

var _ sdk.Msg = &MsgAddAdmin{}

func NewMsgAddAdmin(creator, admin sdk.AccAddress) *MsgAddAdmin {
	return &MsgAddAdmin{
		Creator: creator.String(),
		Admin:   admin.String(),
	}
}

func (msg *MsgAddAdmin) Route() string {
	return RouterKey
}

func (msg *MsgAddAdmin) Type() string {
	return "AddAdmin"
}

func (msg *MsgAddAdmin) GetSigners() []sdk.AccAddress {
	creator, err := sdk.AccAddressFromBech32(msg.Creator)
	if err != nil {
		panic(err)
	}
	return []sdk.AccAddress{creator}
}

func (msg *MsgAddAdmin) GetSignBytes() []byte {
	bz := ModuleCdc.MustMarshalJSON(msg)
	return sdk.MustSortJSON(bz)
}

func (msg *MsgAddAdmin) ValidateBasic() error {
	_, err := sdk.AccAddressFromBech32(msg.Creator)
	if err != nil {
		return sdkerrors.Wrapf(sdkerrors.ErrInvalidAddress, "invalid creator address (%s)", err)
	}
	_, err = sdk.AccAddressFromBech32(msg.Admin)
	if err != nil {
		return sdkerrors.Wrapf(sdkerrors.ErrInvalidAddress, "invalid admin address (%s)", err)
	}
	return nil
}
