package types

import (
	"errors"
	"fmt"
	"strings"
	time "time"

	sdkerrors "cosmossdk.io/errors"
	evidencetypes "github.com/cosmos/cosmos-sdk/x/evidence/types"
	govv1beta1 "github.com/cosmos/cosmos-sdk/x/gov/types/v1beta1"
	clienttypes "github.com/cosmos/ibc-go/v7/modules/core/02-client/types"
	ccvtypes "github.com/cosmos/interchain-security/x/ccv/types"
)

const (
	ProposalTypeConsumerAddition = "ConsumerAddition"
	ProposalTypeConsumerRemoval  = "ConsumerRemoval"
	ProposalTypeEquivocation     = "Equivocation"
)

var (
	_ govv1beta1.Content = &ConsumerAdditionProposal{}
	_ govv1beta1.Content = &ConsumerRemovalProposal{}
	_ govv1beta1.Content = &EquivocationProposal{}
)

func init() {
	govv1beta1.RegisterProposalType(ProposalTypeConsumerAddition)
	govv1beta1.RegisterProposalType(ProposalTypeConsumerRemoval)
	govv1beta1.RegisterProposalType(ProposalTypeEquivocation)
}

// NewConsumerAdditionProposal creates a new consumer addition proposal.
func NewConsumerAdditionProposal(title, description, chainID string,
	initialHeight clienttypes.Height, genesisHash, binaryHash []byte,
	spawnTime time.Time,
	consumerRedistributionFraction string,
	blocksPerDistributionTransmission,
	historicalEntries int64,
	ccvTimeoutPeriod time.Duration,
	transferTimeoutPeriod time.Duration,
	unbondingPeriod time.Duration,
) govv1beta1.Content {
	return &ConsumerAdditionProposal{
		Title:                             title,
		Description:                       description,
		ChainId:                           chainID,
		InitialHeight:                     initialHeight,
		GenesisHash:                       genesisHash,
		BinaryHash:                        binaryHash,
		SpawnTime:                         spawnTime,
		ConsumerRedistributionFraction:    consumerRedistributionFraction,
		BlocksPerDistributionTransmission: blocksPerDistributionTransmission,
		HistoricalEntries:                 historicalEntries,
		CcvTimeoutPeriod:                  ccvTimeoutPeriod,
		TransferTimeoutPeriod:             transferTimeoutPeriod,
		UnbondingPeriod:                   unbondingPeriod,
	}
}

// GetTitle returns the title of a consumer addition proposal.
func (cccp *ConsumerAdditionProposal) GetTitle() string { return cccp.Title }

// GetDescription returns the description of a consumer addition proposal.
func (cccp *ConsumerAdditionProposal) GetDescription() string { return cccp.Description }

// ProposalRoute returns the routing key of a consumer addition proposal.
func (cccp *ConsumerAdditionProposal) ProposalRoute() string { return RouterKey }

// ProposalType returns the type of a consumer addition proposal.
func (cccp *ConsumerAdditionProposal) ProposalType() string {
	return ProposalTypeConsumerAddition
}

// ValidateBasic runs basic stateless validity checks
func (cccp *ConsumerAdditionProposal) ValidateBasic() error {
	if err := govv1beta1.ValidateAbstract(cccp); err != nil {
		return err
	}

	if strings.TrimSpace(cccp.ChainId) == "" {
		return sdkerrors.Wrap(ErrInvalidConsumerAdditionProposal, "consumer chain id must not be blank")
	}

	if cccp.InitialHeight.IsZero() {
		return sdkerrors.Wrap(ErrInvalidConsumerAdditionProposal, "initial height cannot be zero")
	}

	if len(cccp.GenesisHash) == 0 {
		return sdkerrors.Wrap(ErrInvalidConsumerAdditionProposal, "genesis hash cannot be empty")
	}
	if len(cccp.BinaryHash) == 0 {
		return sdkerrors.Wrap(ErrInvalidConsumerAdditionProposal, "binary hash cannot be empty")
	}

	if cccp.SpawnTime.IsZero() {
		return sdkerrors.Wrap(ErrInvalidConsumerAdditionProposal, "spawn time cannot be zero")
	}

	if err := ccvtypes.ValidateStringFraction(cccp.ConsumerRedistributionFraction); err != nil {
		return sdkerrors.Wrapf(ErrInvalidConsumerAdditionProposal, "consumer redistribution fraction is invalid: %s", err)
	}

	if err := ccvtypes.ValidatePositiveInt64(cccp.BlocksPerDistributionTransmission); err != nil {
		return sdkerrors.Wrap(ErrInvalidConsumerAdditionProposal, "blocks per distribution transmission cannot be < 1")
	}

	if err := ccvtypes.ValidatePositiveInt64(cccp.HistoricalEntries); err != nil {
		return sdkerrors.Wrap(ErrInvalidConsumerAdditionProposal, "historical entries cannot be < 1")
	}

	if err := ccvtypes.ValidateDuration(cccp.CcvTimeoutPeriod); err != nil {
		return sdkerrors.Wrap(ErrInvalidConsumerAdditionProposal, "ccv timeout period cannot be zero")
	}

	if err := ccvtypes.ValidateDuration(cccp.TransferTimeoutPeriod); err != nil {
		return sdkerrors.Wrap(ErrInvalidConsumerAdditionProposal, "transfer timeout period cannot be zero")
	}

	if err := ccvtypes.ValidateDuration(cccp.UnbondingPeriod); err != nil {
		return sdkerrors.Wrap(ErrInvalidConsumerAdditionProposal, "unbonding period cannot be zero")
	}

	return nil
}

// String returns the string representation of the ConsumerAdditionProposal.
func (cccp *ConsumerAdditionProposal) String() string {
	return fmt.Sprintf(`CreateConsumerChain Proposal
	Title: %s
	Description: %s
	ChainID: %s
	InitialHeight: %s
	GenesisHash: %s
	BinaryHash: %s
	SpawnTime: %s
	ConsumerRedistributionFraction: %s
	BlocksPerDistributionTransmission: %d
	HistoricalEntries: %d
	CcvTimeoutPeriod: %d
	TransferTimeoutPeriod: %d
	UnbondingPeriod: %d`,
		cccp.Title,
		cccp.Description,
		cccp.ChainId,
		cccp.InitialHeight,
		cccp.GenesisHash,
		cccp.BinaryHash,
		cccp.SpawnTime,
		cccp.ConsumerRedistributionFraction,
		cccp.BlocksPerDistributionTransmission,
		cccp.HistoricalEntries,
		cccp.CcvTimeoutPeriod,
		cccp.TransferTimeoutPeriod,
		cccp.UnbondingPeriod)
}

// NewConsumerRemovalProposal creates a new consumer removal proposal.
func NewConsumerRemovalProposal(title, description, chainID string, stopTime time.Time) govv1beta1.Content {
	return &ConsumerRemovalProposal{
		Title:       title,
		Description: description,
		ChainId:     chainID,
		StopTime:    stopTime,
	}
}

// ProposalRoute returns the routing key of a consumer removal proposal.
func (sccp *ConsumerRemovalProposal) ProposalRoute() string { return RouterKey }

// ProposalType returns the type of a consumer removal proposal.
func (sccp *ConsumerRemovalProposal) ProposalType() string { return ProposalTypeConsumerRemoval }

// ValidateBasic runs basic stateless validity checks
func (sccp *ConsumerRemovalProposal) ValidateBasic() error {
	if err := govv1beta1.ValidateAbstract(sccp); err != nil {
		return err
	}

	if strings.TrimSpace(sccp.ChainId) == "" {
		return sdkerrors.Wrap(ErrInvalidConsumerRemovalProp, "consumer chain id must not be blank")
	}

	if sccp.StopTime.IsZero() {
		return sdkerrors.Wrap(ErrInvalidConsumerRemovalProp, "spawn time cannot be zero")
	}
	return nil
}

// NewEquivocationProposal creates a new equivocation proposal.
func NewEquivocationProposal(title, description string, equivocations []*evidencetypes.Equivocation) govv1beta1.Content {
	return &EquivocationProposal{
		Title:         title,
		Description:   description,
		Equivocations: equivocations,
	}
}

// ProposalRoute returns the routing key of an equivocation  proposal.
func (sp *EquivocationProposal) ProposalRoute() string { return RouterKey }

// ProposalType returns the type of a equivocation proposal.
func (sp *EquivocationProposal) ProposalType() string {
	return ProposalTypeEquivocation
}

// ValidateBasic runs basic stateless validity checks
func (sp *EquivocationProposal) ValidateBasic() error {
	if err := govv1beta1.ValidateAbstract(sp); err != nil {
		return err
	}
	if len(sp.Equivocations) == 0 {
		return errors.New("invalid equivocation proposal: empty equivocations")
	}
	for i := 0; i < len(sp.Equivocations); i++ {
		if err := sp.Equivocations[i].ValidateBasic(); err != nil {
			return err
		}
	}
	return nil
}
