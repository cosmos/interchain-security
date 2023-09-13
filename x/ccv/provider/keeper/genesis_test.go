package keeper_test

import (
	"sort"
	"testing"
	"time"

	host "github.com/cosmos/ibc-go/v8/modules/core/24-host"
	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"

	sdk "github.com/cosmos/cosmos-sdk/types"

	"github.com/cosmos/interchain-security/v3/testutil/crypto"
	testkeeper "github.com/cosmos/interchain-security/v3/testutil/keeper"
	"github.com/cosmos/interchain-security/v3/x/ccv/provider/keeper"
	providertypes "github.com/cosmos/interchain-security/v3/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/v3/x/ccv/types"
)

// TestInitAndExportGenesis tests the export and the initialisation of a provider chain genesis
func TestInitAndExportGenesis(t *testing.T) {
	// create a provider chain genesis populated with two consumer chains
	cChainIDs := []string{"c0", "c1"}
	expClientID := "client"
	oneHourFromNow := time.Now().UTC().Add(time.Hour)
	initHeight, vscID := uint64(5), uint64(1)
	ubdIndex := []uint64{0, 1, 2}
	params := providertypes.DefaultParams()

	// create validator keys and addresses for key assignment
	providerCryptoId := crypto.NewCryptoIdentityFromIntSeed(7896)
	provAddr := providerCryptoId.ProviderConsAddress()

	consumerCryptoId := crypto.NewCryptoIdentityFromIntSeed(7897)
	consumerTmPubKey := consumerCryptoId.TMProtoCryptoPublicKey()
	consumerConsAddr := consumerCryptoId.ConsumerConsAddress()

	initTimeoutTimeStamps := []providertypes.InitTimeoutTimestamp{
		{ChainId: cChainIDs[0], Timestamp: uint64(time.Now().UTC().UnixNano()) + 10},
		{ChainId: cChainIDs[1], Timestamp: uint64(time.Now().UTC().UnixNano()) + 15},
	}

	now := time.Now().UTC()
	exportedVscSendTimeStampsC0 := providertypes.ExportedVscSendTimestamp{
		ChainId: "c0",
		VscSendTimestamps: []providertypes.VscSendTimestamp{
			{VscId: 1, Timestamp: now.Add(time.Hour)},
			{VscId: 2, Timestamp: now.Add(2 * time.Hour)},
		},
	}

	exportedVscSendTimeStampsC1 := providertypes.ExportedVscSendTimestamp{
		ChainId: "c1",
		VscSendTimestamps: []providertypes.VscSendTimestamp{
			{VscId: 1, Timestamp: now.Add(-time.Hour)},
			{VscId: 2, Timestamp: now.Add(time.Hour)},
		},
	}

	var exportedVscSendTimeStampsAll []providertypes.ExportedVscSendTimestamp
	exportedVscSendTimeStampsAll = append(exportedVscSendTimeStampsAll, exportedVscSendTimeStampsC0)
	exportedVscSendTimeStampsAll = append(exportedVscSendTimeStampsAll, exportedVscSendTimeStampsC1)

	// create genesis struct
	provGenesis := providertypes.NewGenesisState(vscID,
		[]providertypes.ValsetUpdateIdToHeight{{ValsetUpdateId: vscID, Height: initHeight}},
		[]providertypes.ConsumerState{
			providertypes.NewConsumerStates(
				cChainIDs[0],
				expClientID,
				"channel",
				initHeight,
				*ccv.DefaultGenesisState(),
				[]providertypes.VscUnbondingOps{
					{VscId: vscID, UnbondingOpIds: ubdIndex},
				},
				[]ccv.ValidatorSetChangePacketData{},
				[]string{"slashedValidatorConsAddress"},
			),
			providertypes.NewConsumerStates(
				cChainIDs[1],
				expClientID,
				"",
				0,
				*ccv.DefaultGenesisState(),
				nil,
				[]ccv.ValidatorSetChangePacketData{{ValsetUpdateId: vscID}},
				nil,
			),
		},
		[]providertypes.UnbondingOp{{
			Id:                      vscID,
			UnbondingConsumerChains: []string{cChainIDs[0]},
		}},
		&providertypes.MaturedUnbondingOps{Ids: ubdIndex},
		[]providertypes.ConsumerAdditionProposal{{
			ChainId:   cChainIDs[0],
			SpawnTime: oneHourFromNow,
		}},
		[]providertypes.ConsumerRemovalProposal{{
			ChainId:  cChainIDs[0],
			StopTime: oneHourFromNow,
		}},
		params,
		[]providertypes.ValidatorConsumerPubKey{
			{
				ChainId:      cChainIDs[0],
				ProviderAddr: provAddr.ToSdkConsAddr(),
				ConsumerKey:  &consumerTmPubKey,
			},
		},
		[]providertypes.ValidatorByConsumerAddr{
			{
				ChainId:      cChainIDs[0],
				ProviderAddr: provAddr.ToSdkConsAddr(),
				ConsumerAddr: consumerConsAddr.ToSdkConsAddr(),
			},
		},
		[]providertypes.ConsumerAddrsToPrune{
			{
				ChainId:       cChainIDs[0],
				VscId:         vscID,
				ConsumerAddrs: &providertypes.AddressList{Addresses: [][]byte{consumerConsAddr.ToSdkConsAddr()}},
			},
		},
		initTimeoutTimeStamps,
		exportedVscSendTimeStampsAll,
	)

	// Instantiate in-mem provider keeper with mocks
	pk, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	gomock.InOrder(
		mocks.MockScopedKeeper.EXPECT().GetCapability(
			ctx, host.PortPath(ccv.ProviderPortID),
		).Return(nil, true).Times(1),
		mocks.MockStakingKeeper.EXPECT().GetLastTotalPower(
			ctx).Return(sdk.NewInt(100)).Times(1), // Return total voting power as 100
	)

	// init provider chain
	pk.InitGenesis(ctx, provGenesis)

	// Expect slash meter to be initialized to it's allowance value
	// (replenish fraction * mocked value defined above)
	slashMeter := pk.GetSlashMeter(ctx)
	replenishFraction, err := sdk.NewDecFromStr(pk.GetParams(ctx).SlashMeterReplenishFraction)
	require.NoError(t, err)
	expectedSlashMeterValue := sdk.NewInt(replenishFraction.MulInt(sdk.NewInt(100)).RoundInt64())
	require.Equal(t, expectedSlashMeterValue, slashMeter)

	// Expect slash meter replenishment time candidate to be set to the current block time + replenish period
	expectedCandidate := ctx.BlockTime().Add(pk.GetSlashMeterReplenishPeriod(ctx))
	require.Equal(t, expectedCandidate, pk.GetSlashMeterReplenishTimeCandidate(ctx))

	// check local provider chain states
	ubdOps, found := pk.GetUnbondingOp(ctx, vscID)
	require.True(t, found)
	require.Equal(t, provGenesis.UnbondingOps[0], ubdOps)
	matureUbdOps := pk.GetMaturedUnbondingOps(ctx)
	require.Equal(t, ubdIndex, matureUbdOps)
	chainID, found := pk.GetChannelToChain(ctx, provGenesis.ConsumerStates[0].ChannelId)
	require.True(t, found)
	require.Equal(t, cChainIDs[0], chainID)
	require.Equal(t, vscID, pk.GetValidatorSetUpdateId(ctx))
	height, found := pk.GetValsetUpdateBlockHeight(ctx, vscID)
	require.True(t, found)
	require.Equal(t, initHeight, height)
	addProp, found := pk.GetPendingConsumerAdditionProp(ctx, oneHourFromNow, cChainIDs[0])
	require.True(t, found)
	require.Equal(t, provGenesis.ConsumerAdditionProposals[0], addProp)
	require.True(t, pk.PendingConsumerRemovalPropExists(ctx, cChainIDs[0], oneHourFromNow))
	require.Equal(t, provGenesis.Params, pk.GetParams(ctx))

	gotConsTmPubKey, found := pk.GetValidatorConsumerPubKey(ctx, cChainIDs[0], provAddr)
	require.True(t, found)
	require.Equal(t, consumerTmPubKey, gotConsTmPubKey)

	providerAddr, found := pk.GetValidatorByConsumerAddr(ctx, cChainIDs[0], consumerConsAddr)
	require.True(t, found)
	require.Equal(t, provAddr, providerAddr)

	addrs := pk.GetConsumerAddrsToPrune(ctx, cChainIDs[0], vscID)
	// Expect same list as what was provided in provGenesis
	expectedAddrList := providertypes.AddressList{Addresses: [][]byte{consumerConsAddr.ToSdkConsAddr()}}
	require.Equal(t, expectedAddrList, addrs)

	// check provider chain's consumer chain states
	assertConsumerChainStates(t, ctx, pk, provGenesis.ConsumerStates...)

	// check the exported genesis
	require.Equal(t, provGenesis, pk.ExportGenesis(ctx))

	initTimeoutTimestampInStore := pk.GetAllInitTimeoutTimestamps(ctx)
	sort.Slice(initTimeoutTimestampInStore, func(i, j int) bool {
		return initTimeoutTimestampInStore[i].Timestamp < initTimeoutTimestampInStore[j].Timestamp
	})
	require.Equal(t, initTimeoutTimestampInStore, initTimeoutTimeStamps)

	vscSendTimestampsC0InStore := pk.GetAllVscSendTimestamps(ctx, cChainIDs[0])
	sort.Slice(vscSendTimestampsC0InStore, func(i, j int) bool {
		return vscSendTimestampsC0InStore[i].VscId < vscSendTimestampsC0InStore[j].VscId
	})
	require.Equal(t, vscSendTimestampsC0InStore, exportedVscSendTimeStampsC0.VscSendTimestamps)

	vscSendTimestampsC1InStore := pk.GetAllVscSendTimestamps(ctx, cChainIDs[1])
	sort.Slice(vscSendTimestampsC1InStore, func(i, j int) bool {
		return vscSendTimestampsC1InStore[i].VscId < vscSendTimestampsC1InStore[j].VscId
	})
	require.Equal(t, vscSendTimestampsC1InStore, exportedVscSendTimeStampsC1.VscSendTimestamps)
}

func assertConsumerChainStates(t *testing.T, ctx sdk.Context, pk keeper.Keeper, consumerStates ...providertypes.ConsumerState) {
	t.Helper()
	for _, cs := range consumerStates {
		chainID := cs.ChainId
		gen, found := pk.GetConsumerGenesis(ctx, chainID)
		require.True(t, found)
		require.Equal(t, *ccv.DefaultGenesisState(), gen)

		clientID, found := pk.GetConsumerClientId(ctx, chainID)
		require.True(t, found)
		require.Equal(t, cs.ClientId, clientID)

		if expChan := cs.ChannelId; expChan != "" {
			gotChan, found := pk.GetChainToChannel(ctx, chainID)
			require.True(t, found)
			require.Equal(t, expChan, gotChan)
		}

		if cs.InitialHeight != 0 {
			_, found = pk.GetInitChainHeight(ctx, chainID)
			require.True(t, found)
		}

		if expVSC := cs.GetPendingValsetChanges(); expVSC != nil {
			gotVSC := pk.GetPendingVSCPackets(ctx, chainID)
			require.Equal(t, expVSC, gotVSC)
		}

		for _, ubdOpIdx := range cs.UnbondingOpsIndex {
			ubdIndex, found := pk.GetUnbondingOpIndex(ctx, chainID, ubdOpIdx.VscId)
			require.True(t, found)
			require.Equal(t, ubdOpIdx.UnbondingOpIds, ubdIndex)
		}

		require.Equal(t, cs.SlashDowntimeAck, pk.GetSlashAcks(ctx, chainID))
	}
}
