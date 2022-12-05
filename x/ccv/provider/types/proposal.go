package types

import (
	"fmt"
	"strings"
	time "time"

	sdktypes "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	govtypes "github.com/cosmos/cosmos-sdk/x/gov/types"
	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
)

const (
	ProposalTypeConsumerAddition = "ConsumerAddition"
	ProposalTypeConsumerRemoval  = "ConsumerRemoval"
)

var (
	_ govtypes.Content = &ConsumerAdditionProposal{}
	_ govtypes.Content = &ConsumerRemovalProposal{}
)

func init() {
	govtypes.RegisterProposalType(ProposalTypeConsumerAddition)
	govtypes.RegisterProposalType(ProposalTypeConsumerRemoval)
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
) govtypes.Content {
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
	if err := govtypes.ValidateAbstract(cccp); err != nil {
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

	if _, err := sdktypes.NewDecFromStr(cccp.ConsumerRedistributionFraction); err != nil {
		return sdkerrors.Wrapf(ErrInvalidConsumerAdditionProposal, "consumer redistribution fraction is invalid: %s", err)
	}

	if cccp.BlocksPerDistributionTransmission < 1 {
		return sdkerrors.Wrap(ErrInvalidConsumerAdditionProposal, "blocks per distribution transmission cannot be < 1")
	}

	if cccp.HistoricalEntries < 1 {
		return sdkerrors.Wrap(ErrInvalidConsumerAdditionProposal, "historical entries cannot be < 1")
	}

	zeroDuration := time.Duration(0)
	if cccp.CcvTimeoutPeriod == zeroDuration {
		return sdkerrors.Wrap(ErrInvalidConsumerAdditionProposal, "ccv timeout period cannot be zero")
	}

	if cccp.TransferTimeoutPeriod == zeroDuration {
		return sdkerrors.Wrap(ErrInvalidConsumerAdditionProposal, "transfer timeout period cannot be zero")
	}

	if cccp.UnbondingPeriod == zeroDuration {
		return sdkerrors.Wrap(ErrInvalidConsumerAdditionProposal, "unbonding period cannot be zero")
	}

	// TODO: sanity check these params
	if cccp.CcvTimeoutPeriod > cccp.UnbondingPeriod {
		return sdkerrors.Wrap(ErrInvalidConsumerAdditionProposal, "ccv timeout period cannot be greater than unbonding period")
	}
	// TODO: sanity check these params
	if cccp.TransferTimeoutPeriod > cccp.UnbondingPeriod {
		return sdkerrors.Wrap(ErrInvalidConsumerAdditionProposal, "transfer timeout period cannot be greater than unbonding period")
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
func NewConsumerRemovalProposal(title, description, chainID string, stopTime time.Time) govtypes.Content {
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
	if err := govtypes.ValidateAbstract(sccp); err != nil {
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
