package types

// CCV events
const (
	EventTypeFirstVSCPacket  = "ccv_first_vsc_packet"
	EventTypeFeeDistribution = "ccv_fee_distribution"
	EventTypeSendSlashPacket = "ccv_send_slash_packet"

	AttributeDistributionCurrentHeight = "current_distribution_height"
	AttributeDistributionNextHeight    = "next_distribution_height"
	AttributeDistributionFraction      = "distribution_fraction"
	AttributeDistributionTotal         = "total"
	AttributeDistributionToConsumer    = "consumer_amount"
	AttributeDistributionToProvider    = "provider_amount"

	AttributeValAddress     = "validator_address"
	AttributeValSetUpdateID = "valset_update_id"
	AttributeInfraction     = "infraction"
)
