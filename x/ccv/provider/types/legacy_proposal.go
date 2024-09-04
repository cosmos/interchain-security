package types

import (
	"fmt"
	time "time"

	clienttypes "github.com/cosmos/ibc-go/v8/modules/core/02-client/types"

	evidencetypes "cosmossdk.io/x/evidence/types"
	govv1beta1 "github.com/cosmos/cosmos-sdk/x/gov/types/v1beta1"
)

const (
	ProposalTypeConsumerAddition     = "ConsumerAddition"
	ProposalTypeConsumerRemoval      = "ConsumerRemoval"
	ProposalTypeConsumerModification = "ConsumerModification"
	ProposalTypeEquivocation         = "Equivocation"
	ProposalTypeChangeRewardDenoms   = "ChangeRewardDenoms"
)

var (
	_ govv1beta1.Content = &ConsumerAdditionProposal{}
	_ govv1beta1.Content = &ConsumerRemovalProposal{}
	_ govv1beta1.Content = &ConsumerModificationProposal{}
	_ govv1beta1.Content = &ChangeRewardDenomsProposal{}
	_ govv1beta1.Content = &EquivocationProposal{}
)

func init() {
	govv1beta1.RegisterProposalType(ProposalTypeConsumerAddition)
	govv1beta1.RegisterProposalType(ProposalTypeConsumerRemoval)
	govv1beta1.RegisterProposalType(ProposalTypeConsumerModification)
	govv1beta1.RegisterProposalType(ProposalTypeChangeRewardDenoms)
	govv1beta1.RegisterProposalType(ProposalTypeEquivocation)
}

// NewConsumerAdditionProposal creates a new consumer addition proposal.
func NewConsumerAdditionProposal(title, description, chainID string,
	initialHeight clienttypes.Height, genesisHash, binaryHash []byte,
	spawnTime time.Time,
	consumerRedistributionFraction string,
	blocksPerDistributionTransmission int64,
	distributionTransmissionChannel string,
	historicalEntries int64,
	ccvTimeoutPeriod time.Duration,
	transferTimeoutPeriod time.Duration,
	unbondingPeriod time.Duration,
	topN uint32,
	validatorsPowerCap uint32,
	validatorSetCap uint32,
	allowlist []string,
	denylist []string,
	minStake uint64,
	allowInactiveVals bool,
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
		DistributionTransmissionChannel:   distributionTransmissionChannel,
		HistoricalEntries:                 historicalEntries,
		CcvTimeoutPeriod:                  ccvTimeoutPeriod,
		TransferTimeoutPeriod:             transferTimeoutPeriod,
		UnbondingPeriod:                   unbondingPeriod,
		Top_N:                             topN,
		ValidatorsPowerCap:                validatorsPowerCap,
		ValidatorSetCap:                   validatorSetCap,
		Allowlist:                         allowlist,
		Denylist:                          denylist,
		MinStake:                          minStake,
		AllowInactiveVals:                 allowInactiveVals,
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
	return fmt.Errorf("ConsumerAdditionProposal is deprecated")
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
	DistributionTransmissionChannel: %s
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
		cccp.DistributionTransmissionChannel,
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
	return fmt.Errorf("ConsumerRemovalProposal is deprecated")
}

// NewConsumerModificationProposal creates a new consumer modification proposal.
func NewConsumerModificationProposal(title, description, chainID string,
	topN uint32,
	validatorsPowerCap uint32,
	validatorSetCap uint32,
	allowlist []string,
	denylist []string,
	minStake uint64,
	allowInactiveVals bool,
) govv1beta1.Content {
	return &ConsumerModificationProposal{
		Title:              title,
		Description:        description,
		ChainId:            chainID,
		Top_N:              topN,
		ValidatorsPowerCap: validatorsPowerCap,
		ValidatorSetCap:    validatorSetCap,
		Allowlist:          allowlist,
		Denylist:           denylist,
		MinStake:           minStake,
		AllowInactiveVals:  allowInactiveVals,
	}
}

// ProposalRoute returns the routing key of a consumer modification proposal.
func (cccp *ConsumerModificationProposal) ProposalRoute() string { return RouterKey }

// ProposalType returns the type of the consumer modification proposal.
func (cccp *ConsumerModificationProposal) ProposalType() string {
	return ProposalTypeConsumerModification
}

// ValidateBasic runs basic stateless validity checks
func (cccp *ConsumerModificationProposal) ValidateBasic() error {
	return fmt.Errorf("ConsumerModificationProposal is deprecated")
}

// NewEquivocationProposal creates a new equivocation proposal.
// [DEPRECATED]: do not use because equivocations can be submitted
// and verified automatically on the provider.
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
	return fmt.Errorf("EquivocationProposal is deprecated")
}

func NewChangeRewardDenomsProposal(title, description string,
	denomsToAdd, denomsToRemove []string,
) govv1beta1.Content {
	return &ChangeRewardDenomsProposal{
		Title:          title,
		Description:    description,
		DenomsToAdd:    denomsToAdd,
		DenomsToRemove: denomsToRemove,
	}
}

// ProposalRoute returns the routing key of a change reward denoms proposal.
func (crdp *ChangeRewardDenomsProposal) ProposalRoute() string { return RouterKey }

// ProposalType returns the type of a change reward denoms proposal.
func (crdp *ChangeRewardDenomsProposal) ProposalType() string {
	return ProposalTypeChangeRewardDenoms
}

// ValidateBasic runs basic stateless validity checks on a ChangeRewardDenomsProposal.
func (crdp *ChangeRewardDenomsProposal) ValidateBasic() error {
	return fmt.Errorf("ChangeRewardDenomsProposal is deprecated")
}
