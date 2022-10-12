package types

import (
	"fmt"

	"github.com/cosmos/cosmos-sdk/codec/types"
	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	distrTypes "github.com/cosmos/cosmos-sdk/x/distribution/types"
	govtypes "github.com/cosmos/cosmos-sdk/x/gov/types"
	paramChange "github.com/cosmos/cosmos-sdk/x/params/types/proposal"
	upgradeTypes "github.com/cosmos/cosmos-sdk/x/upgrade/types"
	clientUpdate "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	"github.com/gogo/protobuf/proto"
	"gopkg.in/yaml.v2"
)

var _ sdk.Msg = &MsgSubmitProposal{}

func NewMsgSubmitProposal(content govtypes.Content, proposer sdk.AccAddress) (*MsgSubmitProposal, error) {
	m := &MsgSubmitProposal{
		Proposer: proposer.String(),
	}

	err := m.SetContent(content)
	if err != nil {
		return nil, err
	}
	return m, nil
}

//func (m *MsgSubmitProposal) GetContent() govtypes.Content { // TODO m.Content.GetCachedValue() returns nil!
//	content, ok := m.Content.GetCachedValue().(govtypes.Content)
//	if !ok {
//		return nil
//	}
//	return content
//}

func (m *MsgSubmitProposal) GetContent() govtypes.Content {
	var err error
	switch m.Content.TypeUrl {
	case "/cosmos.gov.v1beta1.TextProposal":
		{
			var textProposal govtypes.TextProposal
			err = proto.Unmarshal(m.Content.Value, &textProposal)
			if err == nil {
				return &textProposal
			}
		}
	case "/cosmos.params.v1beta1.ParameterChangeProposal":
		{
			var paramChangeProposal paramChange.ParameterChangeProposal
			err = proto.Unmarshal(m.Content.Value, &paramChangeProposal)
			if err == nil {
				return &paramChangeProposal
			}
		}
	case "/cosmos.distribution.v1beta1.CommunityPoolSpendProposal":
		{
			var comPoolSpendProposal distrTypes.CommunityPoolSpendProposal
			err = proto.Unmarshal(m.Content.Value, &comPoolSpendProposal)
			if err == nil {
				return &comPoolSpendProposal
			}
		}
	case "/cosmos.upgrade.v1beta1.SoftwareUpgradeProposal":
		{
			var upgradeProposal upgradeTypes.SoftwareUpgradeProposal
			err = proto.Unmarshal(m.Content.Value, &upgradeProposal)
			if err == nil {
				return &upgradeProposal
			}
		}
	case "/cosmos.upgrade.v1beta1.CancelSoftwareUpgradeProposal":
		{
			var cancelUpgradeProposal upgradeTypes.CancelSoftwareUpgradeProposal
			err = proto.Unmarshal(m.Content.Value, &cancelUpgradeProposal)
			if err == nil {
				return &cancelUpgradeProposal
			}
		}
	case "/ibc.core.client.v1.ClientUpdateProposal":
		{
			var clientUpdateProposal clientUpdate.ClientUpdateProposal
			err = proto.Unmarshal(m.Content.Value, &clientUpdateProposal)
			if err == nil {
				return &clientUpdateProposal
			}
		}
	}

	return nil
}

func (m *MsgSubmitProposal) SetContent(content govtypes.Content) error {
	msg, ok := content.(proto.Message)
	if !ok {
		return fmt.Errorf("can't proto marshal %T", msg)
	}
	any, err := types.NewAnyWithValue(msg)
	if err != nil {
		return err
	}
	m.Content = any
	return nil
}

func (m *MsgSubmitProposal) Route() string {
	return RouterKey
}

func (m *MsgSubmitProposal) Type() string {
	return "SubmitProposal"
}

func (m *MsgSubmitProposal) GetSigners() []sdk.AccAddress {
	proposer, err := sdk.AccAddressFromBech32(m.Proposer)
	if err != nil {
		panic(err)
	}
	return []sdk.AccAddress{proposer}
}

func (m *MsgSubmitProposal) GetSignBytes() []byte {
	bz := govtypes.ModuleCdc.MustMarshalJSON(m)
	return sdk.MustSortJSON(bz)
}

// String implements the Stringer interface
func (m *MsgSubmitProposal) String() string {
	out, _ := yaml.Marshal(m)
	return string(out)
}

// ValidateBasic implements Msg
func (m *MsgSubmitProposal) ValidateBasic() error {
	if m.Proposer == "" {
		return sdkerrors.Wrap(sdkerrors.ErrInvalidAddress, m.Proposer)
	}

	content := m.GetContent()
	if content == nil {
		return sdkerrors.Wrap(govtypes.ErrInvalidProposalContent, "missing content")
	}
	if !govtypes.IsValidProposalType(content.ProposalType()) {
		return sdkerrors.Wrap(govtypes.ErrInvalidProposalType, content.ProposalType())
	}
	if err := content.ValidateBasic(); err != nil {
		return err
	}

	return nil
}
