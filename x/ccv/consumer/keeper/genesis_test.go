package keeper_test

import (
	"testing"
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	host "github.com/cosmos/ibc-go/v3/modules/core/24-host"
	testkeeper "github.com/cosmos/interchain-security/testutil/keeper"
	consumerkeeper "github.com/cosmos/interchain-security/x/ccv/consumer/keeper"
	"github.com/cosmos/interchain-security/x/ccv/consumer/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"
	abci "github.com/tendermint/tendermint/abci/types"
	tmtypes "github.com/tendermint/tendermint/types"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"
	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"

	testutil "github.com/cosmos/interchain-security/testutil/keeper"
)

func TestInitGenesis(t *testing.T) {
	// Channel ID to established provider
	channelIDToProvider := "channelIDToProvider"
	clientIDToProvider := "tendermint-07"

	// create params for a new chain
	params := types.NewParams(true, types.DefaultBlocksPerDistributionTransmission, "", "")

	// create consumer chain states exported into genesis
	// restartHeight := uint64(0)
	matPacket := consumertypes.MaturingVSCPacket{
		VscId:        uint64(1),
		MaturityTime: uint64(time.Now().UnixNano()),
	}

	// generate validator public key
	pubKey, err := testutil.GenPubKey()
	require.NoError(t, err)

	// create validator set with single validator
	validator := tmtypes.NewValidator(pubKey, 1)
	slashRequests := consumertypes.SlashRequests{
		Requests: []consumertypes.SlashRequest{{Infraction: stakingtypes.Downtime}},
	}
	// create consensus state using a single validator
	consensusState := testutil.GetConsensusState(clientIDToProvider, time.Time{}, validator)

	testCases := []struct {
		name         string
		malleate     func(sdk.Context, testutil.MockedKeepers)
		genesis      *consumertypes.GenesisState // input statest
		assertStates func(sdk.Context, consumerkeeper.Keeper, *consumertypes.GenesisState)
	}{
		{
			name: "restart a new chain",
			malleate: func(ctx sdk.Context, mocks testutil.MockedKeepers) {
				gomock.InOrder(
					expectGetCapabilityMock(ctx, mocks),
					expectCreateClientMock(ctx, mocks, "", clientIDToProvider, validator),
				)
			},
			genesis: consumertypes.NewInitialGenesisState(testutil.GetClientState(""), consensusState,
				[]abci.ValidatorUpdate{tmtypes.TM2PB.ValidatorUpdate(validator)}, slashRequests, params),

			assertStates: func(ctx sdk.Context, ck consumerkeeper.Keeper, gs *consumertypes.GenesisState) {
				require.Equal(t, gs.Params, ck.GetParams(ctx))
				require.Equal(t, ccv.ConsumerPortID, ck.GetPort(ctx))

				ubdTime, found := ck.GetUnbondingTime(ctx)
				require.True(t, found)
				require.Equal(t, gs.ProviderClientState.UnbondingPeriod, ubdTime)

				require.Zero(t, ck.GetHeightValsetUpdateID(ctx, uint64(ctx.BlockHeight())))

				cid, ok := ck.GetProviderClientID(ctx)
				require.True(t, ok)
				require.Equal(t, clientIDToProvider, cid)
			},
		}, {
			name: "restart a chain with channel already established",
			malleate: func(ctx sdk.Context, mocks testutil.MockedKeepers) {
				gomock.InOrder(
					expectGetCapabilityMock(ctx, mocks),
					expectLatestConsensusStateMock(ctx, mocks, clientIDToProvider, validator),
					expectGetClientStateMock(ctx, mocks, "", clientIDToProvider),
				)
			},
			genesis: consumertypes.NewRestartGenesisState(clientIDToProvider, channelIDToProvider,
				[]consumertypes.MaturingVSCPacket{matPacket},
				[]abci.ValidatorUpdate{tmtypes.TM2PB.ValidatorUpdate(validator)},
				[]consumertypes.HeightToValsetUpdateID{{ValsetUpdateId: matPacket.VscId, Height: uint64(0)}},
				[]consumertypes.OutstandingDowntime{{ValidatorConsensusAddress: sdk.ConsAddress(validator.Bytes()).String()}},
				params,
			),
			assertStates: func(ctx sdk.Context, ck consumerkeeper.Keeper, gs *consumertypes.GenesisState) {
				require.Equal(t, gs.Params, ck.GetParams(ctx))
				require.Equal(t, ccv.ConsumerPortID, ck.GetPort(ctx))

				ubdTime, found := ck.GetUnbondingTime(ctx)
				require.True(t, found)
				require.Equal(t, testutil.GetClientState("").UnbondingPeriod, ubdTime)

				// export staet to genesis
				require.Equal(t, matPacket.VscId, ck.GetHeightValsetUpdateID(ctx, uint64(0)))

				require.Equal(t, matPacket.MaturityTime, ck.GetPacketMaturityTime(ctx, matPacket.VscId))
				require.Equal(t, gs.Params, ck.GetParams(ctx))
			},
		},
	}

	// Instantiate in-mem consumer keeper with mocks
	ctrl := gomock.NewController(t)
	defer ctrl.Finish()

	keeperParams := testkeeper.NewInMemKeeperParams(t)
	mocks := testkeeper.NewMockedKeepers(ctrl)
	ctx := keeperParams.Ctx

	// explicitly register public key interface
	testkeeper.RegisterSdkCryptoCodecInterfaces(&keeperParams)
	consumerKeeper := testkeeper.NewInMemConsumerKeeper(keeperParams, mocks)
	consumerKeeper.SetParams(ctx, params)

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {

			// test setup
			tc.malleate(ctx, mocks)

			// init states
			consumerKeeper.InitGenesis(ctx, tc.genesis)

			// check the states against genesis used
			tc.assertStates(ctx, consumerKeeper, tc.genesis)
		})
	}
}

func TestExportGenesis(t *testing.T) {

	clientIDToProvider := "tendermint-07"
	channelIDToProvider := "channelIDToProvider"

	// define the states exported into genesis
	slashRequests := consumertypes.SlashRequests{
		Requests: []consumertypes.SlashRequest{{Infraction: stakingtypes.Downtime}},
	}
	restartHeight := uint64(0)
	matPacket := consumertypes.MaturingVSCPacket{
		VscId:        uint64(1),
		MaturityTime: uint64(time.Now().UnixNano()),
	}

	params := types.NewParams(true, types.DefaultBlocksPerDistributionTransmission, "", "")

	// create a single validator
	pubKey := ed25519.GenPrivKey().PubKey()
	tmPK, err := cryptocodec.ToTmPubKeyInterface(pubKey)
	require.NoError(t, err)
	validator := tmtypes.NewValidator(tmPK, 1)

	// create consensus state using a single validator
	consensusState := testutil.GetConsensusState(clientIDToProvider, time.Time{}, validator)

	testCases := []struct {
		name       string
		malleate   func(sdk.Context, consumerkeeper.Keeper, testutil.MockedKeepers)
		expGenesis *consumertypes.GenesisState
	}{
		{
			name: "export a new chain",
			malleate: func(ctx sdk.Context, ck consumerkeeper.Keeper, mocks testutil.MockedKeepers) {
				// populate the states used by a new consumer chain
				cVal, err := consumertypes.NewCCValidator(validator.Address.Bytes(), 1, pubKey)
				require.NoError(t, err)
				ck.SetCCValidator(ctx, cVal)
				ck.SetProviderClientID(ctx, clientIDToProvider)
				ck.SetPendingSlashRequests(
					ctx,
					slashRequests,
				)

				// set the mock calls executed during the export
				gomock.InOrder(
					expectGetClientStateMock(ctx, mocks, "", clientIDToProvider),
					expectLatestConsensusStateMock(ctx, mocks, clientIDToProvider, validator),
				)
			},

			expGenesis: consumertypes.NewInitialGenesisState(testutil.GetClientState(""), consensusState,
				[]abci.ValidatorUpdate{tmtypes.TM2PB.ValidatorUpdate(validator)}, slashRequests, params),
		},
		{
			name: "export a chain that has an established CCV channel",
			malleate: func(ctx sdk.Context, ck consumerkeeper.Keeper, mocks testutil.MockedKeepers) {
				// populate the states used by a running chain
				cVal, err := consumertypes.NewCCValidator(validator.Address.Bytes(), 1, pubKey)
				require.NoError(t, err)
				ck.SetCCValidator(ctx, cVal)
				ck.SetOutstandingDowntime(ctx, sdk.ConsAddress(validator.Address.Bytes()))

				// populate the required states to simulate a completed handshake
				ck.SetProviderClientID(ctx, clientIDToProvider)
				ck.SetProviderChannel(ctx, channelIDToProvider)
				ck.SetHeightValsetUpdateID(ctx, restartHeight, matPacket.VscId)
				ck.SetPacketMaturityTime(ctx, matPacket.VscId, matPacket.MaturityTime)
			},
			expGenesis: consumertypes.NewRestartGenesisState(
				clientIDToProvider,
				channelIDToProvider,
				[]consumertypes.MaturingVSCPacket{matPacket},
				[]abci.ValidatorUpdate{tmtypes.TM2PB.ValidatorUpdate(validator)},
				[]types.HeightToValsetUpdateID{{Height: restartHeight, ValsetUpdateId: matPacket.VscId}},
				[]consumertypes.OutstandingDowntime{{ValidatorConsensusAddress: sdk.ConsAddress(validator.Address.Bytes()).String()}},
				params,
			),
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			// instantiate in-mem consumer keeper with mocks
			ctrl := gomock.NewController(t)
			defer ctrl.Finish()

			keeperParams := testkeeper.NewInMemKeeperParams(t)
			mocks := testkeeper.NewMockedKeepers(ctrl)
			ctx := keeperParams.Ctx

			// explicitly register public key interface
			testkeeper.RegisterSdkCryptoCodecInterfaces(&keeperParams)
			consumerKeeper := testkeeper.NewInMemConsumerKeeper(keeperParams, mocks)
			consumerKeeper.SetParams(ctx, params)

			// test setup
			tc.malleate(ctx, consumerKeeper, mocks)

			// export staet to genesis
			gotGen := consumerKeeper.ExportGenesis(ctx)

			// check the obtained genesis
			require.EqualValues(t, tc.expGenesis, gotGen)
		})
	}
}

func expectLatestConsensusStateMock(ctx sdk.Context, mocks testutil.MockedKeepers, clientID string, vals ...*tmtypes.Validator) *gomock.Call {
	consState := testutil.GetConsensusState(clientID, time.Time{}, vals...)
	return mocks.MockClientKeeper.EXPECT().
		GetLatestClientConsensusState(ctx, clientID).Return(consState, true).Times(1)
}

func expectGetClientStateMock(ctx sdk.Context, mocks testutil.MockedKeepers, chainID, clientID string) *gomock.Call {
	cs := testutil.GetClientState(chainID)
	return mocks.MockClientKeeper.EXPECT().GetClientState(ctx, clientID).Return(cs, true).Times(1)
}

func expectCreateClientMock(ctx sdk.Context, mocks testutil.MockedKeepers, chainID, clientID string, vals ...*tmtypes.Validator) *gomock.Call {
	cs := testutil.GetClientState(chainID)
	consState := testutil.GetConsensusState(clientID, time.Time{}, vals...)

	return mocks.MockClientKeeper.EXPECT().CreateClient(ctx, cs, consState).Return(clientID, nil).Times(1)
}

func expectGetCapabilityMock(ctx sdk.Context, mocks testutil.MockedKeepers) *gomock.Call {
	return mocks.MockScopedKeeper.EXPECT().GetCapability(
		ctx, host.PortPath(ccv.ConsumerPortID),
	).Return(nil, true).Times(1)
}
