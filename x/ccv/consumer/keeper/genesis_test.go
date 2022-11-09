package keeper_test

import (
	"testing"
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	commitmenttypes "github.com/cosmos/ibc-go/v3/modules/core/23-commitment/types"
	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"
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

// TestInitGenesis tests that a consumer chain is correctly initialised from genesis.
// It covers the cases where a chain is new or restarted which means that
// its CCV channel is already established.
func TestInitGenesis(t *testing.T) {
	// create states to initialise a consumer chain from genesis

	// create provider channel and client ids
	provChannelID := "ChannelID"
	provClientID := "tendermint-07"
	// generate validator public key
	pubKey, err := testutil.GenPubKey()
	require.NoError(t, err)
	// create validator set with single validator
	validator := tmtypes.NewValidator(pubKey, 1)
	// create a provider consensus state using a single validator
	provConsState := ibctmtypes.NewConsensusState(
		time.Time{},
		commitmenttypes.NewMerkleRoot([]byte("apphash")),
		tmtypes.NewValidatorSet([]*tmtypes.Validator{validator}).Hash()[:],
	)
	// create a provider client state
	provClientState := ibctmtypes.NewClientState(
		"provider",
		ibctmtypes.DefaultTrustLevel,
		0,
		stakingtypes.DefaultUnbondingTime,
		time.Second*10,
		clienttypes.Height{},
		commitmenttypes.GetSDKSpecs(),
		[]string{"upgrade", "upgradedIBCState"},
		true,
		true,
	)
	slashRequests := consumertypes.SlashRequests{
		Requests: []consumertypes.SlashRequest{{Infraction: stakingtypes.Downtime}},
	}
	matPacket := consumertypes.MaturingVSCPacket{
		VscId:        uint64(1),
		MaturityTime: uint64(time.Now().UnixNano()),
	}

	// create parameters for a new chain
	params := types.NewParams(true,
		types.DefaultBlocksPerDistributionTransmission,
		"",
		"",
		ccv.DefaultCCVTimeoutPeriod,
		consumertypes.DefaultTransferTimeoutPeriod,
		consumertypes.DefaultConsumerRedistributeFrac,
		consumertypes.DefaultHistoricalEntries,
		consumertypes.DefaultConsumerUnbondingPeriod,
	)

	// define two test cases which respectively create a genesis struct, use it to call InitGenesis
	// and finally check that the genesis states are imported in the consumer keeper stores
	testCases := []struct {
		name         string
		malleate     func(sdk.Context, testutil.MockedKeepers)
		genesis      *consumertypes.GenesisState
		assertStates func(sdk.Context, consumerkeeper.Keeper, *consumertypes.GenesisState)
	}{
		{
			name: "restart a new chain",
			malleate: func(ctx sdk.Context, mocks testutil.MockedKeepers) {
				gomock.InOrder(
					testkeeper.ExpectGetCapabilityMock(ctx, mocks),
					testkeeper.ExpectCreateClientMock(ctx, mocks, provClientID, provClientState, provConsState),
				)
			},
			// create a genesis for a new chain
			genesis: consumertypes.NewInitialGenesisState(
				provClientState,
				provConsState,
				[]abci.ValidatorUpdate{tmtypes.TM2PB.ValidatorUpdate(validator)},
				slashRequests,
				params,
			),

			assertStates: func(ctx sdk.Context, ck consumerkeeper.Keeper, gs *consumertypes.GenesisState) {
				require.Equal(t, gs.Params, ck.GetParams(ctx))
				require.Equal(t, ccv.ConsumerPortID, ck.GetPort(ctx))

				ubdPeriod := ck.GetUnbondingPeriod(ctx)
				require.Equal(t, consumertypes.DefaultConsumerUnbondingPeriod, ubdPeriod)

				require.Zero(t, ck.GetHeightValsetUpdateID(ctx, uint64(ctx.BlockHeight())))

				cid, ok := ck.GetProviderClientID(ctx)
				require.True(t, ok)
				require.Equal(t, provClientID, cid)
			},
		}, {
			name: "restart a chain with an already established channel",
			malleate: func(ctx sdk.Context, mocks testutil.MockedKeepers) {
				gomock.InOrder(
					testkeeper.ExpectGetCapabilityMock(ctx, mocks),
					testkeeper.ExpectLatestConsensusStateMock(ctx, mocks, provClientID, provConsState),
				)
			},
			// create a genesis for a restarted chain
			genesis: &consumertypes.GenesisState{
				ProviderClientId:       provClientID,
				ProviderChannelId:      provChannelID,
				Params:                 params,
				NewChain:               false,
				ProviderClientState:    provClientState,
				ProviderConsensusState: provConsState,
				InitialValSet:          []abci.ValidatorUpdate{tmtypes.TM2PB.ValidatorUpdate(validator)},
				OutstandingDowntimeSlashing: []consumertypes.OutstandingDowntime{
					{ValidatorConsensusAddress: sdk.ConsAddress(validator.Bytes()).String()},
				},
				HeightToValsetUpdateId: []consumertypes.HeightToValsetUpdateID{
					{ValsetUpdateId: matPacket.VscId, Height: uint64(0)},
				},
				MaturingPackets: []consumertypes.MaturingVSCPacket{matPacket},
			},
			assertStates: func(ctx sdk.Context, ck consumerkeeper.Keeper, gs *consumertypes.GenesisState) {
				require.Equal(t, gs.Params, ck.GetParams(ctx))
				require.Equal(t, ccv.ConsumerPortID, ck.GetPort(ctx))

				ubdPeriod := ck.GetUnbondingPeriod(ctx)
				require.Equal(t, consumertypes.DefaultConsumerUnbondingPeriod, ubdPeriod)

				// export states to genesis
				require.Equal(t, matPacket.VscId, ck.GetHeightValsetUpdateID(ctx, uint64(0)))

				require.Equal(t, matPacket.MaturityTime, ck.GetPacketMaturityTime(ctx, matPacket.VscId))
				require.Equal(t, gs.Params, ck.GetParams(ctx))
			},
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {

			keeperParams := testkeeper.NewInMemKeeperParams(t)
			// Explicitly register codec with public key interface
			keeperParams.RegisterSdkCryptoCodecInterfaces()
			consumerKeeper, ctx, ctrl, mocks := testkeeper.GetConsumerKeeperAndCtx(t, keeperParams)
			defer ctrl.Finish()

			// test setup
			tc.malleate(ctx, mocks)

			// init chain states
			consumerKeeper.InitGenesis(ctx, tc.genesis)

			// assert consumer keeper states
			tc.assertStates(ctx, consumerKeeper, tc.genesis)
		})
	}
}

// TestExportGenesis tests that a consumer chain genesis is correctly exported to genesis
// It covers the cases where the chain's CCV channel is or isn't established
func TestExportGenesis(t *testing.T) {
	// create consumer chain states to be stored and exported to genesis

	// create provider channel and client ids
	provClientID := "tendermint-07"
	provChannelID := "provChannelID"
	slashRequests := consumertypes.SlashRequests{
		Requests: []consumertypes.SlashRequest{{Infraction: stakingtypes.Downtime}},
	}
	restartHeight := uint64(0)
	matPacket := consumertypes.MaturingVSCPacket{
		VscId:        uint64(1),
		MaturityTime: uint64(time.Now().UnixNano()),
	}

	params := types.NewParams(
		true,
		types.DefaultBlocksPerDistributionTransmission,
		"",
		"",
		ccv.DefaultCCVTimeoutPeriod,
		consumertypes.DefaultTransferTimeoutPeriod,
		consumertypes.DefaultConsumerRedistributeFrac,
		consumertypes.DefaultHistoricalEntries,
		consumertypes.DefaultConsumerUnbondingPeriod,
	)

	// create a single validator
	pubKey := ed25519.GenPrivKey().PubKey()
	tmPK, err := cryptocodec.ToTmPubKeyInterface(pubKey)
	require.NoError(t, err)
	validator := tmtypes.NewValidator(tmPK, 1)
	// create a provider consensus state using a single validator
	provConsState := ibctmtypes.NewConsensusState(
		time.Time{},
		commitmenttypes.NewMerkleRoot([]byte("apphash")),
		tmtypes.NewValidatorSet([]*tmtypes.Validator{validator}).Hash()[:],
	)
	// create a provider client state
	provClientState := ibctmtypes.NewClientState(
		"provider",
		ibctmtypes.DefaultTrustLevel,
		0,
		stakingtypes.DefaultUnbondingTime,
		time.Second*10,
		clienttypes.Height{},
		commitmenttypes.GetSDKSpecs(),
		[]string{"upgrade", "upgradedIBCState"},
		true,
		true,
	)

	// define two test cases which respectively populate the consumer chain store
	// using the states declared above then call ExportGenesis to finally check
	// that the resulting genesis struct stores this same states
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
				ck.SetProviderClientID(ctx, provClientID)
				ck.SetPendingSlashRequests(
					ctx,
					slashRequests,
				)

				// set the mock calls executed during the export
				gomock.InOrder(
					testkeeper.ExpectGetClientStateMock(ctx, mocks, provClientID, provClientState),
					testkeeper.ExpectLatestConsensusStateMock(ctx, mocks, provClientID, provConsState),
				)
			},

			expGenesis: consumertypes.NewInitialGenesisState(provClientState, provConsState,
				[]abci.ValidatorUpdate{tmtypes.TM2PB.ValidatorUpdate(validator)}, slashRequests, params),
		},
		{
			name: "export a chain that has an established CCV channel",
			malleate: func(ctx sdk.Context, ck consumerkeeper.Keeper, mocks testutil.MockedKeepers) {
				// populate the states used by a restarted chain
				cVal, err := consumertypes.NewCCValidator(validator.Address.Bytes(), 1, pubKey)
				require.NoError(t, err)
				ck.SetCCValidator(ctx, cVal)
				ck.SetOutstandingDowntime(ctx, sdk.ConsAddress(validator.Address.Bytes()))
				// populate the required states for an established CCV channel
				ck.SetProviderClientID(ctx, provClientID)
				ck.SetProviderChannel(ctx, provChannelID)
				ck.SetHeightValsetUpdateID(ctx, restartHeight, matPacket.VscId)
				ck.SetPacketMaturityTime(ctx, matPacket.VscId, matPacket.MaturityTime)
			},
			expGenesis: consumertypes.NewRestartGenesisState(
				provClientID,
				provChannelID,
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

			keeperParams := testkeeper.NewInMemKeeperParams(t)
			// Explicitly register codec with public key interface
			keeperParams.RegisterSdkCryptoCodecInterfaces()
			consumerKeeper, ctx, ctrl, mocks := testkeeper.GetConsumerKeeperAndCtx(t, keeperParams)
			defer ctrl.Finish()
			consumerKeeper.SetParams(ctx, params)

			// test setup
			tc.malleate(ctx, consumerKeeper, mocks)

			// export states to genesis
			gotGen := consumerKeeper.ExportGenesis(ctx)

			// check obtained genesis
			require.EqualValues(t, tc.expGenesis, gotGen)
		})
	}
}
