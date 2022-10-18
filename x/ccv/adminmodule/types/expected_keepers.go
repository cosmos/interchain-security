package types

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
)

type ConsumerKeeper interface {
	GetProviderChannel(ctx sdk.Context) (string, bool)
	GetConnectionHops(ctx sdk.Context, srcPort, srcChan string) ([]string, error)
	GetProviderGovernanceAddress(ctx sdk.Context) (string, bool)
}

type ICAHostKeeper interface {
	GetInterchainAccountAddress(ctx sdk.Context, connectionID, portID string) (string, bool)
}
