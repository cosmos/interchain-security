package keeper_test

import (
	"testing"
	"time"

	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"
	sdk "github.com/cosmos/cosmos-sdk/types"
	host "github.com/cosmos/ibc-go/v4/modules/core/24-host"
	testkeeper "github.com/cosmos/interchain-security/testutil/keeper"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
	"github.com/cosmos/interchain-security/x/ccv/provider/keeper"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"
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

	// create validator keys and addresses for key assignement
	provAddr := sdk.ConsAddress(ed25519.GenPrivKey().PubKey().Address().Bytes())
	consPubKey := ed25519.GenPrivKey().PubKey()
	consTmPubKey, err := cryptocodec.ToTmProtoPublicKey(consPubKey)
	require.NoError(t, err)
	consAddr := sdk.ConsAddress(consPubKey.Address().Bytes())

	// create genesis struct
	provGenesis := providertypes.NewGenesisState(vscID,
		[]providertypes.ValsetUpdateIdToHeight{{ValsetUpdateId: vscID, Height: initHeight}},
		[]providertypes.ConsumerState{
			providertypes.NewConsumerStates(
				cChainIDs[0],
				expClientID,
				"channel",
				initHeight,
				*consumertypes.DefaultGenesisState(),
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
				*consumertypes.DefaultGenesisState(),
				nil,
				[]ccv.ValidatorSetChangePacketData{{ValsetUpdateId: vscID}},
				nil,
			),
		},
		[]providertypes.UnbondingOp{{
			Id:                      vscID,
			UnbondingConsumerChains: []string{cChainIDs[0]},
		}},
		&ccv.MaturedUnbondingOps{Ids: ubdIndex},
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
				ProviderAddr: provAddr,
				ConsumerKey:  &consTmPubKey,
			},
		},
		[]providertypes.ValidatorByConsumerAddr{
			{
				ChainId:      cChainIDs[0],
				ProviderAddr: provAddr,
				ConsumerAddr: consAddr,
			},
		},
		[]providertypes.ConsumerAddrsToPrune{
			{
				ChainId:       cChainIDs[0],
				VscId:         vscID,
				ConsumerAddrs: &providertypes.AddressList{Addresses: [][]byte{consAddr}},
			},
		},
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
		mocks.MockStakingKeeper.EXPECT().BondDenom(
			ctx).Return("stake").AnyTimes(), // Return bond denom as "stake"
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
	require.True(t, consTmPubKey.Equal(gotConsTmPubKey))

	providerAddr, found := pk.GetValidatorByConsumerAddr(ctx, cChainIDs[0], consAddr)
	require.True(t, found)
	require.Equal(t, provAddr, providerAddr)

	addrs := pk.GetConsumerAddrsToPrune(ctx, cChainIDs[0], vscID)
	require.Equal(t, [][]byte{consAddr}, addrs.Addresses)

	// check provider chain's consumer chain states
	assertConsumerChainStates(ctx, t, pk, provGenesis.ConsumerStates...)

	// check the exported genesis
	require.Equal(t, provGenesis, pk.ExportGenesis(ctx))

}

func assertConsumerChainStates(ctx sdk.Context, t *testing.T, pk keeper.Keeper, consumerStates ...providertypes.ConsumerState) {
	for _, cs := range consumerStates {
		chainID := cs.ChainId
		gen, found := pk.GetConsumerGenesis(ctx, chainID)
		require.True(t, found)
		require.Equal(t, *consumertypes.DefaultGenesisState(), gen)

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
