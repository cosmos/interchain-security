package types

// Provider events
const (
	EventTypeConsumerClientCreated     = "consumer_client_created"
	EventTypeAssignConsumerKey         = "assign_consumer_key"
	EventTypeAddConsumerRewardDenom    = "add_consumer_reward_denom"
	EventTypeRemoveConsumerRewardDenom = "remove_consumer_reward_denom"
	EventTypeExecuteConsumerChainSlash = "execute_consumer_chain_slash"
	AttributeInfractionHeight          = "infraction_height"
	AttributeInitialHeight             = "initial_height"
	AttributeInitializationTimeout     = "initialization_timeout"
	AttributeTrustingPeriod            = "trusting_period"
	AttributeUnbondingPeriod           = "unbonding_period"
	AttributeProviderValidatorAddress  = "provider_validator_address"
	AttributeConsumerConsensusPubKey   = "consumer_consensus_pub_key"
	AttributeConsumerRewardDenom       = "consumer_reward_denom"
)
