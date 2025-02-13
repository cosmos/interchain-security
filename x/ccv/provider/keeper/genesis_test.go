package keeper_test

import (
	"testing"
	"time"

	host "github.com/cosmos/ibc-go/v9/modules/core/24-host"
	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"

	"cosmossdk.io/math"

	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	"github.com/cosmos/interchain-security/v7/testutil/crypto"
	testkeeper "github.com/cosmos/interchain-security/v7/testutil/keeper"
	"github.com/cosmos/interchain-security/v7/x/ccv/provider/keeper"
	providertypes "github.com/cosmos/interchain-security/v7/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/v7/x/ccv/types"
)

// TestInitAndExportGenesis tests the export and the initialisation of a provider chain genesis
func TestInitAndExportGenesis(t *testing.T) {
	// create a provider chain genesis populated with two consumer chains
	cChainIDs := []string{"c0", "c1"}
	expClientID := "client"
	oneHourFromNow := time.Now().UTC().Add(time.Hour)
	initHeight, vscID := uint64(5), uint64(1)
	params := providertypes.DefaultParams()

	// create validator keys and addresses for key assignment
	providerCryptoId := crypto.NewCryptoIdentityFromIntSeed(7896)
	provAddr := providerCryptoId.ProviderConsAddress()
	provVal := providerCryptoId.SDKStakingValidator()
	provPubKey, err := provVal.CmtConsPublicKey()
	require.NoError(t, err)

	consumerCryptoId := crypto.NewCryptoIdentityFromIntSeed(7897)
	consumerTmPubKey := consumerCryptoId.TMProtoCryptoPublicKey()
	consumerConsAddr := consumerCryptoId.ConsumerConsAddress()

	// create genesis struct
	provGenesis := providertypes.NewGenesisState(vscID,
		[]providertypes.ValsetUpdateIdToHeight{{ValsetUpdateId: vscID, Height: initHeight}},
		[]providertypes.ConsumerState{
			providertypes.NewConsumerStates(
				cChainIDs[0],
				expClientID,
				"channel",
				initHeight,
				*ccv.DefaultConsumerGenesisState(),
				[]ccv.ValidatorSetChangePacketData{},
				[]string{"slashedValidatorConsAddress"},
				providertypes.CONSUMER_PHASE_LAUNCHED,
			),
			providertypes.NewConsumerStates(
				cChainIDs[1],
				expClientID,
				"",
				0,
				*ccv.DefaultConsumerGenesisState(),
				[]ccv.ValidatorSetChangePacketData{{ValsetUpdateId: vscID}},
				nil,
				providertypes.CONSUMER_PHASE_LAUNCHED,
			),
		},
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
		[]providertypes.ConsumerAddrsToPruneV2{
			{
				ChainId:       cChainIDs[0],
				PruneTs:       oneHourFromNow,
				ConsumerAddrs: &providertypes.AddressList{Addresses: [][]byte{consumerConsAddr.ToSdkConsAddr()}},
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
			ctx).Return(math.NewInt(100), nil).Times(1), // Return total voting power as 100
	)

	mocks.MockStakingKeeper.EXPECT().GetBondedValidatorsByPower(gomock.Any()).Return(
		[]stakingtypes.Validator{
			provVal,
		}, nil).AnyTimes()

	valAddr, err := sdk.ValAddressFromBech32(provVal.GetOperator())
	require.NoError(t, err)
	mocks.MockStakingKeeper.EXPECT().GetLastValidatorPower(gomock.Any(), valAddr).
		Return(int64(100), nil).AnyTimes()

	// init provider chain
	pk.InitGenesis(ctx, provGenesis)

	// Expect slash meter to be initialized to it's allowance value
	// (replenish fraction * mocked value defined above)
	slashMeter := pk.GetSlashMeter(ctx)
	replenishFraction, err := math.LegacyNewDecFromStr(pk.GetParams(ctx).SlashMeterReplenishFraction)
	require.NoError(t, err)
	expectedSlashMeterValue := math.NewInt(replenishFraction.MulInt(math.NewInt(100)).RoundInt64())
	require.Equal(t, expectedSlashMeterValue, slashMeter)

	// Expect slash meter replenishment time candidate to be set to the current block time + replenish period
	expectedCandidate := ctx.BlockTime().Add(pk.GetSlashMeterReplenishPeriod(ctx))
	require.Equal(t, expectedCandidate, pk.GetSlashMeterReplenishTimeCandidate(ctx))

	// check local provider chain states
	chainID, found := pk.GetChannelIdToConsumerId(ctx, provGenesis.ConsumerStates[0].ChannelId)
	require.True(t, found)
	require.Equal(t, cChainIDs[0], chainID)
	require.Equal(t, vscID, pk.GetValidatorSetUpdateId(ctx))
	height, found := pk.GetValsetUpdateBlockHeight(ctx, vscID)
	require.True(t, found)
	require.Equal(t, initHeight, height)
	require.Equal(t, provGenesis.Params, pk.GetParams(ctx))

	providerConsensusValSet, err := pk.GetLastProviderConsensusValSet(ctx)
	require.NoError(t, err)
	require.Equal(t,
		[]providertypes.ConsensusValidator{{
			ProviderConsAddr: provAddr.Address,
			Power:            100,
			PublicKey:        &provPubKey,
		}},
		providerConsensusValSet,
	)

	gotConsTmPubKey, found := pk.GetValidatorConsumerPubKey(ctx, cChainIDs[0], provAddr)
	require.True(t, found)
	require.Equal(t, consumerTmPubKey, gotConsTmPubKey)

	providerAddr, found := pk.GetValidatorByConsumerAddr(ctx, cChainIDs[0], consumerConsAddr)
	require.True(t, found)
	require.Equal(t, provAddr, providerAddr)

	addrs := pk.GetConsumerAddrsToPrune(ctx, cChainIDs[0], oneHourFromNow)
	// Expect same list as what was provided in provGenesis
	expectedAddrList := providertypes.AddressList{Addresses: [][]byte{consumerConsAddr.ToSdkConsAddr()}}
	require.Equal(t, expectedAddrList, addrs)

	// check provider chain's consumer chain states
	assertConsumerChainStates(t, ctx, pk, provGenesis.ConsumerStates...)

	// check the exported genesis
	require.Equal(t, provGenesis, pk.ExportGenesis(ctx))
}

func assertConsumerChainStates(t *testing.T, ctx sdk.Context, pk keeper.Keeper, consumerStates ...providertypes.ConsumerState) {
	t.Helper()
	for _, cs := range consumerStates {
		chainID := cs.ChainId
		gen, found := pk.GetConsumerGenesis(ctx, chainID)
		require.True(t, found)
		require.Equal(t, *ccv.DefaultConsumerGenesisState(), gen)

		clientID, found := pk.GetConsumerClientId(ctx, chainID)
		require.True(t, found)
		require.Equal(t, cs.ClientId, clientID)

		if expChan := cs.ChannelId; expChan != "" {
			gotChan, found := pk.GetConsumerIdToChannelId(ctx, chainID)
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

		require.Equal(t, cs.SlashDowntimeAck, pk.GetSlashAcks(ctx, chainID))
	}
}
