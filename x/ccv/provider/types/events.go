package types

// Provider events
const (
	EventTypeConsumerClientCreated     = "consumer_client_created"
	EventTypeAssignConsumerKey         = "assign_consumer_key"
	EventTypeChangeConsumerRewardDenom = "change_consumer_reward_denom"
	EventTypeExecuteConsumerChainSlash = "execute_consumer_chain_slash"
	EventTypeSetConsumerCommissionRate = "set_consumer_commission_rate"
	EventTypeOptIn                     = "opt_in"
	EventTypeOptOut                    = "opt_out"
	AttributeInfractionHeight          = "infraction_height"
	AttributeInitialHeight             = "initial_height"
	AttributeTrustingPeriod            = "trusting_period"
	AttributeUnbondingPeriod           = "unbonding_period"
	AttributeProviderValidatorAddress  = "provider_validator_address"
	AttributeConsumerConsensusPubKey   = "consumer_consensus_pub_key"
	AttributeAddConsumerRewardDenom    = "add_consumer_reward_denom"
	AttributeRemoveConsumerRewardDenom = "remove_consumer_reward_denom"
	AttributeConsumerCommissionRate    = "consumer_commission_rate"
	AttributeConsumerId                = "consumer_chain_id"
)
