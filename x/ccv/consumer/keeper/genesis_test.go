package keeper_test

import (
	"testing"
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	clienttypes "github.com/cosmos/ibc-go/v4/modules/core/02-client/types"
	commitmenttypes "github.com/cosmos/ibc-go/v4/modules/core/23-commitment/types"
	ibctmtypes "github.com/cosmos/ibc-go/v4/modules/light-clients/07-tendermint/types"
	"github.com/cosmos/interchain-security/v2/testutil/crypto"
	testkeeper "github.com/cosmos/interchain-security/v2/testutil/keeper"
	consumerkeeper "github.com/cosmos/interchain-security/x/consumer/keeper"
	ccv "github.com/cosmos/interchain-security/x/types"
	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"
	abci "github.com/tendermint/tendermint/abci/types"
	tmtypes "github.com/tendermint/tendermint/types"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"
)

// TestInitGenesis tests that a consumer chain is correctly initialised from genesis.
// It covers the start of a new chain, the restart of a chain during the CCV channel handshake
// and finally the restart of chain when the CCV channel is already established.
func TestInitGenesis(t *testing.T) {
	// mock the consumer genesis state values
	provClientID := "tendermint-07"
	provChannelID := "ChannelID"

	vscID := uint64(0)
	blockHeight := uint64(0)

	// create validator set
	cId := crypto.NewCryptoIdentityFromIntSeed(234234)
	pubKey := cId.TMCryptoPubKey()
	validator := tmtypes.NewValidator(pubKey, 1)
	abciValidator := abci.Validator{Address: pubKey.Address(), Power: int64(1)}
	valset := []abci.ValidatorUpdate{tmtypes.TM2PB.ValidatorUpdate(validator)}

	// create ibc client and last consensus states
	provConsState := ibctmtypes.NewConsensusState(
		time.Time{},
		commitmenttypes.NewMerkleRoot([]byte("apphash")),
		tmtypes.NewValidatorSet([]*tmtypes.Validator{validator}).Hash(),
	)

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

	matPackets := []ccv.MaturingVSCPacket{
		{
			VscId:        1,
			MaturityTime: time.Now().UTC(),
		},
	}
	pendingDataPackets := ccv.ConsumerPacketDataList{
		List: []ccv.ConsumerPacketData{
			{
				Type: ccv.SlashPacket,
				Data: &ccv.ConsumerPacketData_SlashPacketData{
					SlashPacketData: ccv.NewSlashPacketData(abciValidator, vscID, stakingtypes.Downtime),
				},
			},
			{
				Type: ccv.VscMaturedPacket,
				Data: &ccv.ConsumerPacketData_VscMaturedPacketData{
					VscMaturedPacketData: ccv.NewVSCMaturedPacketData(1),
				},
			},
		},
	}
	// mock height to valset update ID values
	defaultHeightValsetUpdateIDs := []ccv.HeightToValsetUpdateID{
		{ValsetUpdateId: vscID, Height: blockHeight},
	}
	updatedHeightValsetUpdateIDs := append(defaultHeightValsetUpdateIDs,
		ccv.HeightToValsetUpdateID{ValsetUpdateId: vscID + 1, Height: blockHeight + 1},
	)

	// create default parameters for a new chain
	params := ccv.DefaultConsumerParams()
	params.Enabled = true

	// define three test cases which respectively create a genesis struct, use it to call InitGenesis
	// and finally check that the genesis states are successfully imported in the consumer keeper stores
	testCases := []struct {
		name         string
		malleate     func(sdk.Context, testkeeper.MockedKeepers)
		genesis      *ccv.ConsumerGenesisState
		assertStates func(sdk.Context, consumerkeeper.Keeper, *ccv.ConsumerGenesisState)
	}{
		{
			"start a new chain",
			func(ctx sdk.Context, mocks testkeeper.MockedKeepers) {
				gomock.InOrder(
					testkeeper.ExpectGetCapabilityMock(ctx, mocks, 1),
					testkeeper.ExpectCreateClientMock(ctx, mocks, provClientID, provClientState, provConsState),
					testkeeper.ExpectGetCapabilityMock(ctx, mocks, 1),
				)
			},
			ccv.NewInitialConsumerGenesisState(
				provClientState,
				provConsState,
				valset,
				params,
			),
			func(ctx sdk.Context, ck consumerkeeper.Keeper, gs *ccv.ConsumerGenesisState) {
				assertConsumerPortIsBound(t, ctx, &ck)

				assertProviderClientID(t, ctx, &ck, provClientID)
				assertHeightValsetUpdateIDs(t, ctx, &ck, defaultHeightValsetUpdateIDs)

				require.Equal(t, validator.Address.Bytes(), ck.GetAllCCValidator(ctx)[0].Address)
				require.Equal(t, gs.Params, ck.GetConsumerParams(ctx))
			},
		}, {
			"restart a chain without an established CCV channel",
			func(ctx sdk.Context, mocks testkeeper.MockedKeepers) {
				gomock.InOrder(
					testkeeper.ExpectGetCapabilityMock(ctx, mocks, 2),
				)
			},
			ccv.NewRestartConsumerGenesisState(
				provClientID,
				"",
				matPackets,
				valset,
				defaultHeightValsetUpdateIDs,
				pendingDataPackets,
				nil,
				ccv.LastTransmissionBlockHeight{},
				params,
			),
			func(ctx sdk.Context, ck consumerkeeper.Keeper, gs *ccv.ConsumerGenesisState) {
				assertConsumerPortIsBound(t, ctx, &ck)

				require.Equal(t, pendingDataPackets, ck.GetPendingPackets(ctx))
				assertHeightValsetUpdateIDs(t, ctx, &ck, defaultHeightValsetUpdateIDs)
				assertProviderClientID(t, ctx, &ck, provClientID)
				require.Equal(t, validator.Address.Bytes(), ck.GetAllCCValidator(ctx)[0].Address)
				require.Equal(t, gs.Params, ck.GetConsumerParams(ctx))
			},
		}, {
			"restart a chain with an established CCV channel",
			func(ctx sdk.Context, mocks testkeeper.MockedKeepers) {
				// simulate a CCV channel handshake completition
				params.DistributionTransmissionChannel = "distribution-channel"
				params.ProviderFeePoolAddrStr = "provider-fee-pool-address"
				gomock.InOrder(
					testkeeper.ExpectGetCapabilityMock(ctx, mocks, 2),
				)
			},
			// create a genesis for a restarted chain
			ccv.NewRestartConsumerGenesisState(
				provClientID,
				provChannelID,
				matPackets,
				valset,
				updatedHeightValsetUpdateIDs,
				pendingDataPackets,
				[]ccv.OutstandingDowntime{
					{ValidatorConsensusAddress: sdk.ConsAddress(validator.Bytes()).String()},
				},
				ccv.LastTransmissionBlockHeight{Height: int64(100)},
				params,
			),
			func(ctx sdk.Context, ck consumerkeeper.Keeper, gs *ccv.ConsumerGenesisState) {
				assertConsumerPortIsBound(t, ctx, &ck)

				gotChannelID, ok := ck.GetProviderChannel(ctx)
				require.True(t, ok)
				require.Equal(t, provChannelID, gotChannelID)

				require.True(t, ck.PacketMaturityTimeExists(ctx, matPackets[0].VscId, matPackets[0].MaturityTime))
				require.Equal(t, pendingDataPackets, ck.GetPendingPackets(ctx))

				require.Equal(t, gs.OutstandingDowntimeSlashing, ck.GetAllOutstandingDowntimes(ctx))

				ltbh := ck.GetLastTransmissionBlockHeight(ctx)
				require.Equal(t, gs.LastTransmissionBlockHeight, ltbh)

				assertHeightValsetUpdateIDs(t, ctx, &ck, updatedHeightValsetUpdateIDs)
				assertProviderClientID(t, ctx, &ck, provClientID)

				require.Equal(t, gs.Params, ck.GetConsumerParams(ctx))
			},
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			keeperParams := testkeeper.NewInMemKeeperParams(t)
			consumerKeeper, ctx, ctrl, mocks := consumerkeeper.GetConsumerKeeperAndCtx(t, keeperParams)
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
// It covers the restart of chain when a CCV channel is or isn't established yet.
func TestExportGenesis(t *testing.T) {
	// create provider channel and client ids
	provClientID := "tendermint-07"
	provChannelID := "provChannelID"

	vscID := uint64(0)
	blockHeight := uint64(0)

	matPackets := []ccv.MaturingVSCPacket{
		{
			VscId:        1,
			MaturityTime: time.Now().UTC(),
		},
	}

	// mock a validator set
	pubKey := ed25519.GenPrivKey().PubKey()
	tmPK, err := cryptocodec.ToTmPubKeyInterface(pubKey)
	require.NoError(t, err)
	validator := tmtypes.NewValidator(tmPK, 1)
	abciValidator := abci.Validator{Address: pubKey.Address(), Power: int64(1)}
	valset := []abci.ValidatorUpdate{tmtypes.TM2PB.ValidatorUpdate(validator)}

	// create pending consumer packets
	consPackets := ccv.ConsumerPacketDataList{
		List: []ccv.ConsumerPacketData{
			{
				Type: ccv.SlashPacket,
				Data: &ccv.ConsumerPacketData_SlashPacketData{
					SlashPacketData: ccv.NewSlashPacketData(abciValidator, vscID, stakingtypes.Downtime),
				},
			},
			{
				Type: ccv.VscMaturedPacket,
				Data: &ccv.ConsumerPacketData_VscMaturedPacketData{
					VscMaturedPacketData: ccv.NewVSCMaturedPacketData(vscID),
				},
			},
		},
	}
	// mock height to valset update ID values
	defaultHeightValsetUpdateIDs := []ccv.HeightToValsetUpdateID{
		{ValsetUpdateId: vscID, Height: blockHeight},
	}
	updatedHeightValsetUpdateIDs := append(defaultHeightValsetUpdateIDs,
		ccv.HeightToValsetUpdateID{ValsetUpdateId: vscID + 1, Height: blockHeight + 1},
	)
	ltbh := ccv.LastTransmissionBlockHeight{Height: int64(1000)}
	// create default parameters for a new chain
	params := ccv.DefaultConsumerParams()
	params.Enabled = true

	// define two test cases which respectively populate the consumer chain store
	// using the states declared above then call ExportGenesis to finally check
	// that the resulting genesis struct contains the same states
	testCases := []struct {
		name       string
		malleate   func(sdk.Context, consumerkeeper.Keeper, testkeeper.MockedKeepers)
		expGenesis *ccv.ConsumerGenesisState
	}{
		{
			"export a chain without an established CCV channel",
			func(ctx sdk.Context, ck consumerkeeper.Keeper, mocks testkeeper.MockedKeepers) {
				// populate the states allowed before a CCV channel is established
				ck.SetProviderClientID(ctx, provClientID)
				cVal, err := ccv.NewCCValidator(validator.Address.Bytes(), 1, pubKey)
				require.NoError(t, err)
				ck.SetCCValidator(ctx, cVal)
				ck.SetParams(ctx, params)

				ck.AppendPendingPacket(ctx, consPackets.List...)
				ck.SetHeightValsetUpdateID(ctx, defaultHeightValsetUpdateIDs[0].Height, defaultHeightValsetUpdateIDs[0].ValsetUpdateId)
			},
			ccv.NewRestartConsumerGenesisState(
				provClientID,
				"",
				nil,
				valset,
				defaultHeightValsetUpdateIDs,
				consPackets,
				nil,
				ccv.LastTransmissionBlockHeight{},
				params,
			),
		},
		{
			"export a chain with an established CCV channel",
			func(ctx sdk.Context, ck consumerkeeper.Keeper, mocks testkeeper.MockedKeepers) {
				ck.SetProviderClientID(ctx, provClientID)
				ck.SetProviderChannel(ctx, provChannelID)

				cVal, err := ccv.NewCCValidator(validator.Address.Bytes(), 1, pubKey)
				require.NoError(t, err)
				ck.SetCCValidator(ctx, cVal)

				ck.SetParams(ctx, params)

				ck.SetHeightValsetUpdateID(ctx, updatedHeightValsetUpdateIDs[0].Height, updatedHeightValsetUpdateIDs[0].ValsetUpdateId)
				ck.SetHeightValsetUpdateID(ctx, updatedHeightValsetUpdateIDs[1].Height, updatedHeightValsetUpdateIDs[1].ValsetUpdateId)

				ck.AppendPendingPacket(ctx, consPackets.List...)

				// populate the required states for an established CCV channel
				ck.SetPacketMaturityTime(ctx, matPackets[0].VscId, matPackets[0].MaturityTime)
				ck.SetOutstandingDowntime(ctx, sdk.ConsAddress(validator.Address.Bytes()))
				ck.SetLastTransmissionBlockHeight(ctx, ltbh)
			},
			ccv.NewRestartConsumerGenesisState(
				provClientID,
				provChannelID,
				matPackets,
				valset,
				updatedHeightValsetUpdateIDs,
				consPackets,
				[]ccv.OutstandingDowntime{
					{ValidatorConsensusAddress: sdk.ConsAddress(validator.Address.Bytes()).String()},
				},
				ltbh,
				params,
			),
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			keeperParams := testkeeper.NewInMemKeeperParams(t)
			consumerKeeper, ctx, ctrl, mocks := consumerkeeper.GetConsumerKeeperAndCtx(t, keeperParams)
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

// assert that the default CCV consumer port ID is stored and bounded
func assertConsumerPortIsBound(t *testing.T, ctx sdk.Context, ck *consumerkeeper.Keeper) {
	t.Helper()
	require.Equal(t, ck.GetPort(ctx), string(ccv.ConsumerPortID))
	require.True(t, ck.IsBound(ctx, ccv.ConsumerPortID))
}

// assert that the given client ID matches the provider client ID in the store
func assertProviderClientID(t *testing.T, ctx sdk.Context, ck *consumerkeeper.Keeper, clientID string) {
	t.Helper()
	cid, ok := ck.GetProviderClientID(ctx)
	require.True(t, ok)
	require.Equal(t, clientID, cid)
}

// assert that the given input match the height to valset update ID mappings in the store
func assertHeightValsetUpdateIDs(t *testing.T, ctx sdk.Context, ck *consumerkeeper.Keeper, heighValsetUpdateIDs []ccv.HeightToValsetUpdateID) {
	t.Helper()
	ctr := 0

	for _, heightToValsetUpdateID := range ck.GetAllHeightToValsetUpdateIDs(ctx) {
		require.Equal(t, heighValsetUpdateIDs[ctr].Height, heightToValsetUpdateID.Height)
		require.Equal(t, heighValsetUpdateIDs[ctr].ValsetUpdateId, heightToValsetUpdateID.ValsetUpdateId)
		ctr++
	}
}
