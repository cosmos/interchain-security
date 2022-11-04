package types

import (
	"fmt"
	"strings"
	time "time"

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
func NewConsumerAdditionProposal(title, description, chainID string, initialHeight clienttypes.Height, genesisHash, binaryHash []byte, spawnTime time.Time) govtypes.Content {
	return &ConsumerAdditionProposal{
		Title:         title,
		Description:   description,
		ChainId:       chainID,
		InitialHeight: initialHeight,
		GenesisHash:   genesisHash,
		BinaryHash:    binaryHash,
		SpawnTime:     spawnTime,
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
	SpawnTime: %s`, cccp.Title, cccp.Description, cccp.ChainId, cccp.InitialHeight, cccp.GenesisHash, cccp.BinaryHash, cccp.SpawnTime)
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
