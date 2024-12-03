package chainsuite

import (
	"time"
)

type Metadata struct {
	Name        string `json:"name"`
	Description string `json:"description"`
	Metadata    string `json:"metadata"`
}

type ConsumerChain struct {
	ChainID            string   `json:"chain_id"`
	ClientID           string   `json:"client_id"`
	TopN               int      `json:"top_N"`
	MinPowerInTopN     string   `json:"min_power_in_top_N"`
	ValidatorsPowerCap int      `json:"validators_power_cap"`
	ValidatorSetCap    int      `json:"validator_set_cap"`
	Allowlist          []string `json:"allowlist"`
	Denylist           []string `json:"denylist"`
	Phase              string   `json:"phase"`
	Metadata           Metadata `json:"metadata"`
	MinStake           string   `json:"min_stake"`
	AllowInactiveVals  bool     `json:"allow_inactive_vals"`
	ConsumerID         string   `json:"consumer_id"`
}

type Pagination struct {
	NextKey interface{} `json:"next_key"`
	Total   string      `json:"total"`
}

type ListConsumerChainsResponse struct {
	Chains     []ConsumerChain `json:"chains"`
	Pagination Pagination      `json:"pagination"`
}

type ConsumerResponse struct {
	ChainID            string             `json:"chain_id"`
	ConsumerID         string             `json:"consumer_id"`
	InitParams         InitParams         `json:"init_params"`
	Metadata           Metadata           `json:"metadata"`
	OwnerAddress       string             `json:"owner_address"`
	Phase              string             `json:"phase"`
	PowerShapingParams PowerShapingParams `json:"power_shaping_params"`
}

type InitParams struct {
	BinaryHash                        string        `json:"binary_hash"`
	BlocksPerDistributionTransmission string        `json:"blocks_per_distribution_transmission"`
	CCVTimeoutPeriod                  string        `json:"ccv_timeout_period"`
	ConsumerRedistributionFraction    string        `json:"consumer_redistribution_fraction"`
	DistributionTransmissionChannel   string        `json:"distribution_transmission_channel"`
	GenesisHash                       string        `json:"genesis_hash"`
	HistoricalEntries                 string        `json:"historical_entries"`
	InitialHeight                     InitialHeight `json:"initial_height"`
	SpawnTime                         time.Time     `json:"spawn_time"`
	TransferTimeoutPeriod             string        `json:"transfer_timeout_period"`
	UnbondingPeriod                   string        `json:"unbonding_period"`
}

type InitialHeight struct {
	RevisionHeight string `json:"revision_height"`
	RevisionNumber string `json:"revision_number"`
}

type PowerShapingParams struct {
	AllowInactiveVals  bool     `json:"allow_inactive_vals"`
	Allowlist          []string `json:"allowlist"`
	Denylist           []string `json:"denylist"`
	MinStake           string   `json:"min_stake"`
	TopN               int      `json:"top_N"`
	ValidatorSetCap    int      `json:"validator_set_cap"`
	ValidatorsPowerCap int      `json:"validators_power_cap"`
}

type Params struct {
	Enabled                           bool     `json:"enabled"`
	BlocksPerDistributionTransmission string   `json:"blocks_per_distribution_transmission"`
	DistributionTransmissionChannel   string   `json:"distribution_transmission_channel"`
	ProviderFeePoolAddrStr            string   `json:"provider_fee_pool_addr_str"`
	CCVTimeoutPeriod                  string   `json:"ccv_timeout_period"`
	TransferTimeoutPeriod             string   `json:"transfer_timeout_period"`
	ConsumerRedistributionFraction    string   `json:"consumer_redistribution_fraction"`
	HistoricalEntries                 string   `json:"historical_entries"`
	UnbondingPeriod                   string   `json:"unbonding_period"`
	SoftOptOutThreshold               string   `json:"soft_opt_out_threshold"`
	RewardDenoms                      []string `json:"reward_denoms"`
	ProviderRewardDenoms              []string `json:"provider_reward_denoms"`
	RetryDelayPeriod                  string   `json:"retry_delay_period"`
}

type TrustLevel struct {
	Numerator   string `json:"numerator"`
	Denominator string `json:"denominator"`
}

type Height struct {
	RevisionNumber string `json:"revision_number"`
	RevisionHeight string `json:"revision_height"`
}

type ClientState struct {
	ChainID                      string      `json:"chain_id"`
	TrustLevel                   TrustLevel  `json:"trust_level"`
	TrustingPeriod               string      `json:"trusting_period"`  // Duration as string (e.g., "100s")
	UnbondingPeriod              string      `json:"unbonding_period"` // Duration as string (e.g., "100s")
	MaxClockDrift                string      `json:"max_clock_drift"`  // Duration as string (e.g., "100s")
	FrozenHeight                 Height      `json:"frozen_height"`
	LatestHeight                 Height      `json:"latest_height"`
	ProofSpecs                   []ProofSpec `json:"proof_specs"`
	UpgradePath                  []string    `json:"upgrade_path"`
	AllowUpdateAfterExpiry       bool        `json:"allow_update_after_expiry"`
	AllowUpdateAfterMisbehaviour bool        `json:"allow_update_after_misbehaviour"`
}

type Root struct {
	Hash string `json:"hash"`
}

type ConsensusState struct {
	Timestamp          string `json:"timestamp"`
	Root               Root   `json:"root"`
	NextValidatorsHash string `json:"next_validators_hash"`
}

type ProofSpec struct {
	LeafSpec  LeafSpec  `json:"leaf_spec"`
	InnerSpec InnerSpec `json:"inner_spec"`
}

type LeafSpec struct {
	Hash         string `json:"hash"`
	PrehashValue string `json:"prehash_value"`
	Length       string `json:"length"`
	Prefix       string `json:"prefix"`
}

type InnerSpec struct {
	ChildOrder      []int  `json:"child_order"`
	ChildSize       int    `json:"child_size"`
	MinPrefixLength int    `json:"min_prefix_length"`
	MaxPrefixLength int    `json:"max_prefix_length"`
	Hash            string `json:"hash"`
}

type Provider struct {
	ClientState    ClientState        `json:"client_state"`
	ConsensusState ConsensusState     `json:"consensus_state"`
	InitialValSet  []InitialValidator `json:"initial_val_set"`
}

type InitialValidator struct {
	PubKey PubKey `json:"pub_key"`
	Power  string `json:"power"`
}

type PubKey struct {
	Ed25519 string `json:"ed25519"`
}

type ConsumerGenesisResponse struct {
	Params   Params   `json:"params"`
	NewChain bool     `json:"new_chain"`
	Provider Provider `json:"provider"`
}

type OptInValidatorsResponse struct {
	ValidatorsProviderAddresses []string `json:"validators_provider_addresses"`
}

type ValidatorConsumerAddressResponse struct {
	ConsumerAddress string `json:"consumer_address"`
}

type ValidatorProviderAddressResponse struct {
	ProviderAddress string `json:"provider_address"`
}
