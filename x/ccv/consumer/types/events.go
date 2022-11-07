package types

// CCV events
const (
	EventTypeFirstVSCPacket  = "ccv_first_vsc_packet"
	EventTypeFeeDistribution = "ccv_fee_distribution"

	AttributeDistributionCurrentHeight = "current_distribution_height"
	AttributeDistributionNextHeight    = "next_distribution_height"
	AttributeDistributionFraction      = "distribution_fraction"
	AttributeDistributionTotal         = "total"
	AttributeDistributionToConsumer    = "consumer_amount"
	AttributeDistributionToProvider    = "provider_amount"
)
