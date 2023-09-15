package keeper_test

import (
	"sort"
	"testing"
	"time"

	"github.com/cometbft/cometbft/abci/types"
	host "github.com/cosmos/ibc-go/v7/modules/core/24-host"
	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"

	sdk "github.com/cosmos/cosmos-sdk/types"

	_07_tendermint "github.com/cosmos/ibc-go/v7/modules/light-clients/07-tendermint"
	"github.com/cosmos/interchain-security/v3/testutil/crypto"
	testkeeper "github.com/cosmos/interchain-security/v3/testutil/keeper"
	"github.com/cosmos/interchain-security/v3/x/ccv/provider/keeper"
	providertypes "github.com/cosmos/interchain-security/v3/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/v3/x/ccv/types"
)

func TestConsumerConsumerGenesisState(t *testing.T) {
	state := ccv.ConsumerGenesisState{
		Params: ccv.ConsumerParams{
			Enabled:                           true,
			BlocksPerDistributionTransmission: 23,
			DistributionTransmissionChannel:   "trans channel",
			ProviderFeePoolAddrStr:            "pool addr",
			CcvTimeoutPeriod:                  time.Duration(time.Duration.Seconds(3)),
			TransferTimeoutPeriod:             time.Duration(time.Duration.Seconds(3)),
			ConsumerRedistributionFraction:    "red fraction",
			HistoricalEntries:                 3,
			UnbondingPeriod:                   time.Duration(time.Duration.Seconds(3)),
			SoftOptOutThreshold:               "soft threshold",
			RewardDenoms:                      []string{"reward2", "reward1"},
			ProviderRewardDenoms:              []string{"prd1", "prd3"},
		},
		ProviderClientId:  "aID",
		ProviderChannelId: "chanelID",
		NewChain:          false,
		// ProviderClientState filled in on new chain, nil on restart.
		ProviderClientState:         &_07_tendermint.ClientState{ChainId: "my_provClStChainID"},
		ProviderConsensusState:      &_07_tendermint.ConsensusState{Timestamp: time.Unix(10003, 3)},
		MaturingPackets:             []ccv.MaturingVSCPacket{{VscId: 42}},
		InitialValSet:               []types.ValidatorUpdate{{Power: 4}, {Power: 2}},
		HeightToValsetUpdateId:      []ccv.HeightToValsetUpdateID{{Height: 2}, {Height: 5}},
		OutstandingDowntimeSlashing: []ccv.OutstandingDowntime{{ValidatorConsensusAddress: "addr1"}, {ValidatorConsensusAddress: "addr3"}},
		PendingConsumerPackets:      ccv.ConsumerPacketDataList{List: []ccv.ConsumerPacketData{{Type: 45}}},
		LastTransmissionBlockHeight: ccv.LastTransmissionBlockHeight{Height: 982734},
		PreCCV:                      true,
	}

	buf := make([]byte, state.Size())
	len, err := state.MarshalToSizedBuffer(buf)
	require.NoError(t, err, "Error marshalling genesis state %s", err)
	require.True(t, len > 0, "Len of buffer is 0")
	// This is the marshalled bytestring before the renaming (ccv.GenesisState, ccv.Params)
	expectedFromNew := []byte{0xa, 0x62, 0x8, 0x1, 0x10, 0x17, 0x1a, 0xd, 0x74, 0x72, 0x61, 0x6e, 0x73, 0x20, 0x63, 0x68, 0x61, 0x6e, 0x6e, 0x65, 0x6c, 0x22, 0x9, 0x70, 0x6f, 0x6f, 0x6c, 0x20, 0x61, 0x64, 0x64, 0x72, 0x2a, 0x0, 0x32, 0x0, 0x3a, 0xc, 0x72, 0x65, 0x64, 0x20, 0x66, 0x72, 0x61, 0x63, 0x74, 0x69, 0x6f, 0x6e, 0x40, 0x3, 0x4a, 0x0, 0x52, 0xe, 0x73, 0x6f, 0x66, 0x74, 0x20, 0x74, 0x68, 0x72, 0x65, 0x73, 0x68, 0x6f, 0x6c, 0x64, 0x5a, 0x7, 0x72, 0x65, 0x77, 0x61, 0x72, 0x64, 0x32, 0x5a, 0x7, 0x72, 0x65, 0x77, 0x61, 0x72, 0x64, 0x31, 0x62, 0x4, 0x70, 0x72, 0x64, 0x31, 0x62, 0x4, 0x70, 0x72, 0x64, 0x33, 0x12, 0x3, 0x61, 0x49, 0x44, 0x1a, 0x8, 0x63, 0x68, 0x61, 0x6e, 0x65, 0x6c, 0x49, 0x44, 0x2a, 0x20, 0xa, 0x12, 0x6d, 0x79, 0x5f, 0x70, 0x72, 0x6f, 0x76, 0x43, 0x6c, 0x53, 0x74, 0x43, 0x68, 0x61, 0x69, 0x6e, 0x49, 0x44, 0x12, 0x0, 0x1a, 0x0, 0x22, 0x0, 0x2a, 0x0, 0x32, 0x0, 0x3a, 0x0, 0x32, 0x9, 0xa, 0x5, 0x8, 0x93, 0x4e, 0x10, 0x3, 0x12, 0x0, 0x3a, 0xf, 0x8, 0x2a, 0x12, 0xb, 0x8, 0x80, 0x92, 0xb8,
		0xc3, 0x98, 0xfe, 0xff, 0xff, 0xff, 0x1, 0x42, 0x4, 0xa, 0x0, 0x10, 0x4, 0x42, 0x4, 0xa, 0x0, 0x10, 0x2, 0x4a, 0x2, 0x8, 0x2, 0x4a, 0x2, 0x8, 0x5, 0x52, 0x7, 0xa, 0x5, 0x61, 0x64, 0x64, 0x72, 0x31, 0x52, 0x7, 0xa, 0x5, 0x61, 0x64, 0x64, 0x72, 0x33, 0x5a, 0x4, 0xa, 0x2, 0x8, 0x2d, 0x62, 0x4, 0x8, 0xce, 0xfd, 0x3b, 0x68, 0x1}
	require.Equal(t, expectedFromNew, buf)
	newStat := ccv.ConsumerGenesisState{}
	newStat.Unmarshal(expectedFromNew)
	require.Equal(t, newStat.Params.SoftOptOutThreshold, "soft threshold")
}

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
