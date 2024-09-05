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
	EventTypeCreateConsumer            = "create_consumer"
	EventTypeUpdateConsumer            = "update_consumer"

	AttributeInfractionHeight          = "infraction_height"
	AttributeInitialHeight             = "initial_height"
	AttributeTrustingPeriod            = "trusting_period"
	AttributeUnbondingPeriod           = "unbonding_period"
	AttributeProviderValidatorAddress  = "provider_validator_address"
	AttributeConsumerConsensusPubKey   = "consumer_consensus_pub_key"
	AttributeAddConsumerRewardDenom    = "add_consumer_reward_denom"
	AttributeRemoveConsumerRewardDenom = "remove_consumer_reward_denom"
	AttributeSubmitterAddress          = "submitter_address"
	AttributeConsumerCommissionRate    = "consumer_commission_rate"
	AttributeConsumerID                = "consumer_id"
	AttributeConsumerChainID           = "consumer_chain_id"
	AttributeConsumerName              = "consumer_name"
	AttributeConsumerOwner             = "consumer_owner"
	AttributeConsumerSpawnTime         = "consumer_spawn_time"
	AttributeConsumerPhase             = "consumer_phase"
	AttributeConsumerTopN              = "consumer_topn"
)
