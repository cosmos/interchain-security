package keeper

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	ibctesting "github.com/cosmos/ibc-go/v3/testing"
	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
	abci "github.com/tendermint/tendermint/abci/types"
)

// The interface that any provider app must implement to be compatible with e2e tests
type ProviderApp interface {
	ibctesting.TestingApp
	GetProviderKeeper() ProviderKeeper
}

// The interface that any consumer app must implement to be compatible with e2e tests
type ConsumerApp interface {
	ibctesting.TestingApp
	GetConsumerKeeper() ConsumerKeeper
}

// The interface that any consumer keeper must implement to be compatible with e2e tests
type ConsumerKeeper interface {
	InitGenesis(ctx sdk.Context, state *consumertypes.GenesisState) []abci.ValidatorUpdate
	GetProviderClientID(ctx sdk.Context) (string, bool)
	GetDistributionTransmissionChannel(ctx sdk.Context) string
	// TODO: Expand this interface to be referenced by all e2e tests
}

// The interface that any provider keeper must implement to be compatible with e2e tests
type ProviderKeeper interface {
	CreateConsumerClient(ctx sdk.Context, chainID string, initialHeight clienttypes.Height, lockUbdOnTimeout bool) error
	GetConsumerGenesis(ctx sdk.Context, chainID string) (consumertypes.GenesisState, bool)
	GetConsumerClientId(ctx sdk.Context, chainID string) (string, bool)
	// TODO: Expand this interface to be referenced by all e2e tests
}
