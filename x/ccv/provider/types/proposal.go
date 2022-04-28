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
	ProposalTypeCreateConsumerChain = "CreateConsumerChain"
)

var (
	_ govtypes.Content = &CreateConsumerChainProposal{}
)

func init() {
	govtypes.RegisterProposalType(ProposalTypeCreateConsumerChain)
}

// NewCreateConsumerChainProposal creates a new create consumerchain proposal.
func NewCreateConsumerChainProposal(title, description, chainID string, initialHeight clienttypes.Height, genesisHash, binaryHash []byte, spawnTime time.Time) (govtypes.Content, error) {
	return &CreateConsumerChainProposal{
		Title:         title,
		Description:   description,
		ChainId:       chainID,
		InitialHeight: initialHeight,
		GenesisHash:   genesisHash,
		BinaryHash:    binaryHash,
		SpawnTime:     spawnTime,
	}, nil
}

// GetTitle returns the title of a create consumerchain proposal.
func (cccp *CreateConsumerChainProposal) GetTitle() string { return cccp.Title }

// GetDescription returns the description of a create consumerchain proposal.
func (cccp *CreateConsumerChainProposal) GetDescription() string { return cccp.Description }

// ProposalRoute returns the routing key of a create consumerchain proposal.
func (cccp *CreateConsumerChainProposal) ProposalRoute() string { return RouterKey }

// ProposalType returns the type of a create consumerchain proposal.
func (cccp *CreateConsumerChainProposal) ProposalType() string { return ProposalTypeCreateConsumerChain }

// ValidateBasic runs basic stateless validity checks
func (cccp *CreateConsumerChainProposal) ValidateBasic() error {
	if err := govtypes.ValidateAbstract(cccp); err != nil {
		return err
	}

	if strings.TrimSpace(cccp.ChainId) == "" {
		return sdkerrors.Wrap(ErrInvalidProposal, "consumer chain id must not be blank")
	}

	if cccp.InitialHeight.IsZero() {
		return sdkerrors.Wrap(ErrInvalidProposal, "initial height cannot be zero")
	}

	if len(cccp.GenesisHash) == 0 {
		return sdkerrors.Wrap(ErrInvalidProposal, "genesis hash cannot be empty")
	}
	if len(cccp.BinaryHash) == 0 {
		return sdkerrors.Wrap(ErrInvalidProposal, "binary hash cannot be empty")
	}

	if cccp.SpawnTime.IsZero() {
		return sdkerrors.Wrap(ErrInvalidProposal, "spawn time cannot be zero")
	}
	return nil
}

// String returns the string representation of the CreateConsumerChainProposal.
func (cccp *CreateConsumerChainProposal) String() string {
	return fmt.Sprintf(`CreateConsumerChain Proposal
	Title: %s
	Description: %s
	ChainID: %s
	InitialHeight: %s
	GenesisHash: %s
	BinaryHash: %s
	SpawnTime: %s`, cccp.Title, cccp.Description, cccp.ChainId, cccp.InitialHeight, cccp.GenesisHash, cccp.BinaryHash, cccp.SpawnTime)
}
