package types

const (
	// ModuleName defines the CCV module name
	ModuleName = "CCV"

	// Version defines the current version the IBC CCV provider and consumer
	// module supports
	Version = "1"

	// ProviderPortID is the default port id the provider CCV module binds to
	ProviderPortID = "provider"

	// ConsumerPortID is the default port id the consumer CCV module binds to
	ConsumerPortID = "consumer"

	RouterKey = ModuleName

	// StoreKey defines the primary module store key
	StoreKey = ModuleName

	// MemStoreKey defines the in-memory store key
	MemStoreKey = "mem_ccv"
)
