package keeper

import (
	time "time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	capabilitytypes "github.com/cosmos/cosmos-sdk/x/capability/types"
	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	conntypes "github.com/cosmos/ibc-go/v3/modules/core/03-connection/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"
	"github.com/golang/mock/gomock"

	ccv "github.com/cosmos/interchain-security/x/ccv/types"

	extra "github.com/oxyno-zeta/gomock-extra-matcher"
)

//
// A file containing groups of commonly used mock expectations.
// Note: Each group of mock expectations is associated with a single method
// that may be called during unit tests.
//

// GetMocksForCreateConsumerClient returns mock expectations needed to call CreateConsumerClient().
func GetMocksForCreateConsumerClient(ctx sdk.Context, mocks *MockedKeepers,
	expectedChainID string, expectedLatestHeight clienttypes.Height) []*gomock.Call {

	expectations := []*gomock.Call{

		mocks.MockClientKeeper.EXPECT().CreateClient(
			ctx,
			// Allows us to expect a match by field. These are the only two client state values
			// that are dependant on parameters passed to CreateConsumerClient.
			extra.StructMatcher().Field(
				"ChainId", expectedChainID).Field(
				"LatestHeight", expectedLatestHeight,
			),
			gomock.Any(),
		).Return("clientID", nil).Times(1),
	}

	expectations = append(expectations, GetMocksForMakeConsumerGenesis(ctx, mocks, time.Hour)...)
	return expectations
}

// GetMocksForMakeConsumerGenesis returns mock expectations needed to call MakeConsumerGenesis().
func GetMocksForMakeConsumerGenesis(ctx sdk.Context, mocks *MockedKeepers,
	unbondingTimeToInject time.Duration) []*gomock.Call {
	return []*gomock.Call{
		mocks.MockStakingKeeper.EXPECT().UnbondingTime(ctx).Return(unbondingTimeToInject).Times(1),

		mocks.MockClientKeeper.EXPECT().GetSelfConsensusState(ctx,
			clienttypes.GetSelfHeight(ctx)).Return(&ibctmtypes.ConsensusState{}, nil).Times(1),

		mocks.MockStakingKeeper.EXPECT().IterateLastValidatorPowers(ctx, gomock.Any()).Times(1),
	}
}

// GetMocksForSetConsumerChain returns mock expectations needed to call SetConsumerChain().
func GetMocksForSetConsumerChain(ctx sdk.Context, mocks *MockedKeepers,
	chainIDToInject string) []*gomock.Call {
	return []*gomock.Call{
		mocks.MockChannelKeeper.EXPECT().GetChannel(ctx, ccv.ProviderPortID, gomock.Any()).Return(
			channeltypes.Channel{
				State:          channeltypes.OPEN,
				ConnectionHops: []string{"connectionID"},
			},
			true,
		).Times(1),
		mocks.MockConnectionKeeper.EXPECT().GetConnection(ctx, "connectionID").Return(
			conntypes.ConnectionEnd{ClientId: "clientID"}, true,
		).Times(1),
		mocks.MockClientKeeper.EXPECT().GetClientState(ctx, "clientID").Return(
			&ibctmtypes.ClientState{ChainId: chainIDToInject}, true,
		).Times(1),
	}
}

// GetMocksForStopConsumerChain returns mock expectations needed to call StopConsumerChain().
func GetMocksForStopConsumerChain(ctx sdk.Context, mocks *MockedKeepers) []*gomock.Call {
	dummyCap := &capabilitytypes.Capability{}
	return []*gomock.Call{
		mocks.MockChannelKeeper.EXPECT().GetChannel(ctx, ccv.ProviderPortID, "channelID").Return(
			channeltypes.Channel{State: channeltypes.OPEN}, true,
		).Times(1),
		mocks.MockScopedKeeper.EXPECT().GetCapability(ctx, gomock.Any()).Return(dummyCap, true).Times(1),
		mocks.MockChannelKeeper.EXPECT().ChanCloseInit(ctx, ccv.ProviderPortID, "channelID", dummyCap).Times(1),
	}
}
