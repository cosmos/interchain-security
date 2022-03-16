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
	ProposalTypeCreateChildChain = "CreateChildChain"
)

var (
	_ govtypes.Content = &CreateChildChainProposal{}
)

func init() {
	govtypes.RegisterProposalType(ProposalTypeCreateChildChain)
}

// NewCreateChildChainProposal creates a new create childchain proposal.
func NewCreateChildChainProposal(title, description, chainID string, initialHeight clienttypes.Height, genesisHash, binaryHash []byte, spawnTime time.Time) (govtypes.Content, error) {
	return &CreateChildChainProposal{
		Title:         title,
		Description:   description,
		ChainId:       chainID,
		InitialHeight: initialHeight,
		GenesisHash:   genesisHash,
		BinaryHash:    binaryHash,
		SpawnTime:     spawnTime,
	}, nil
}

// GetTitle returns the title of a create childchain proposal.
func (cccp *CreateChildChainProposal) GetTitle() string { return cccp.Title }

// GetDescription returns the description of a create childchain proposal.
func (cccp *CreateChildChainProposal) GetDescription() string { return cccp.Description }

// ProposalRoute returns the routing key of a create childchain proposal.
func (cccp *CreateChildChainProposal) ProposalRoute() string { return RouterKey }

// ProposalType returns the type of a create childchain proposal.
func (cccp *CreateChildChainProposal) ProposalType() string { return ProposalTypeCreateChildChain }

// ValidateBasic runs basic stateless validity checks
func (cccp *CreateChildChainProposal) ValidateBasic() error {
	if err := govtypes.ValidateAbstract(cccp); err != nil {
		return err
	}

	if strings.TrimSpace(cccp.ChainId) == "" {
		return sdkerrors.Wrap(ErrInvalidProposal, "child chain id must not be blank")
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

// String returns the string representation of the CreateChildChainProposal.
func (cccp *CreateChildChainProposal) String() string {
	return fmt.Sprintf(`CreateChildChain Proposal
	Title: %s
	Description: %s
	ChainID: %s
	InitialHeight: %s
	GenesisHash: %s
	BinaryHash: %s
	SpawnTime: %s`, cccp.Title, cccp.Description, cccp.ChainId, cccp.InitialHeight, cccp.GenesisHash, cccp.BinaryHash, cccp.SpawnTime)
}
