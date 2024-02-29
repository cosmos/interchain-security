package types

// Provider events
const (
	EventTypeConsumerClientCreated     = "consumer_client_created"
	EventTypeAssignConsumerKey         = "assign_consumer_key"
	EventTypeAddConsumerRewardDenom    = "add_consumer_reward_denom"
	EventTypeRemoveConsumerRewardDenom = "remove_consumer_reward_denom"
	EventTypeExecuteConsumerChainSlash = "execute_consumer_chain_slash"
	EventTypeSetConsumerCommissionRate = "set_consumer_commission_rate"
	AttributeInfractionHeight          = "infraction_height"
	AttributeInitialHeight             = "initial_height"
	AttributeInitializationTimeout     = "initialization_timeout"
	AttributeTrustingPeriod            = "trusting_period"
	AttributeUnbondingPeriod           = "unbonding_period"
	AttributeProviderValidatorAddress  = "provider_validator_address"
	AttributeConsumerConsensusPubKey   = "consumer_consensus_pub_key"
	AttributeConsumerRewardDenom       = "consumer_reward_denom"
	AttributeConsumerCommissionRate    = "consumer_commission_rate"
	AttributeConsumerChainID           = "consumer_chain_id"
)
