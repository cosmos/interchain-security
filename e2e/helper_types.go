package main

import (
	"time"

	evidencetypes "github.com/cosmos/cosmos-sdk/x/evidence/types"
	clienttypes "github.com/cosmos/ibc-go/v7/modules/core/02-client/types"
)

// ConsumerAdditionProposal body as defined for interchain-security/v3
type ConsumerAdditionProposalJSONV3 struct {
	Title         string             `json:"title"`
	Summary       string             `json:"summary"`
	ChainId       string             `json:"chain_id"`
	InitialHeight clienttypes.Height `json:"initial_height"`
	GenesisHash   []byte             `json:"genesis_hash"`
	BinaryHash    []byte             `json:"binary_hash"`
	SpawnTime     time.Time          `json:"spawn_time"`

	ConsumerRedistributionFraction    string        `json:"consumer_redistribution_fraction"`
	BlocksPerDistributionTransmission int64         `json:"blocks_per_distribution_transmission"`
	DistributionTransmissionChannel   string        `json:"distribution_transmission_channel"`
	HistoricalEntries                 int64         `json:"historical_entries"`
	CcvTimeoutPeriod                  time.Duration `json:"ccv_timeout_period"`
	TransferTimeoutPeriod             time.Duration `json:"transfer_timeout_period"`
	UnbondingPeriod                   time.Duration `json:"unbonding_period"`

	Deposit string `json:"deposit"`
}

// ConsumerRemovalProposal body as defined for interchain-security/v3
type ConsumerRemovalProposalJSONV3 struct {
	Title    string    `json:"title"`
	Summary  string    `json:"summary"`
	ChainId  string    `json:"chain_id"`
	StopTime time.Time `json:"stop_time"`
	Deposit  string    `json:"deposit"`
}

// EquivocationProposal body as defined for interchain-security/v3
type EquivocationProposalJSONV3 struct {
	Summary       string                        `json:"summary"`
	Title         string                        `json:"title,omitempty"`
	Description   string                        `json:"description,omitempty"`
	Equivocations []*evidencetypes.Equivocation `json:"equivocations,omitempty"`
	Deposit       string                        `json:"deposit"`
}

type CCVParams struct {
	Enabled                           bool          `json:"enabled,omitempty"`
	BlocksPerDistributionTransmission int64         `json:"blocks_per_distribution_transmission,omitempty"`
	DistributionTransmissionChannel   string        `json:"distribution_transmission_channel,omitempty"`
	ProviderFeePoolAddrStr            string        `json:"provider_fee_pool_addr_str,omitempty"`
	CcvTimeoutPeriod                  time.Duration `json:"ccv_timeout_period"`
	TransferTimeoutPeriod             time.Duration `json:"transfer_timeout_period"`
	ConsumerRedistributionFraction    string        `json:"consumer_redistribution_fraction,omitempty"`
	HistoricalEntries                 int64         `json:"historical_entries,omitempty"`
	UnbondingPeriod                   time.Duration `json:"unbonding_period"`
	SoftOptOutThreshold               string        `json:"soft_opt_out_threshold,omitempty"`
	RewardDenoms                      []string      `json:"reward_denoms,omitempty"`
	ProviderRewardDenoms              []string      `json:"provider_reward_denoms,omitempty"`
}

// DefaultCCVParameters for ICS v3
var DefaultCCVParams = CCVParams{
	Enabled:                           false,
	BlocksPerDistributionTransmission: 1000,
	DistributionTransmissionChannel:   "",
	ProviderFeePoolAddrStr:            "",
	CcvTimeoutPeriod:                  4 * 7 * 24 * time.Hour, //672h0m0s,
	TransferTimeoutPeriod:             1 * time.Hour,
	ConsumerRedistributionFraction:    "0.75",
	HistoricalEntries:                 10000,
	UnbondingPeriod:                   time.Hour*24*7*3 - 7*24*time.Hour,
	SoftOptOutThreshold:               "0.05",
	RewardDenoms:                      []string{},
	ProviderRewardDenoms:              []string{},
}
