package keeper_test

import (
	"testing"
	"time"

	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"
	sdk "github.com/cosmos/cosmos-sdk/types"
	host "github.com/cosmos/ibc-go/v3/modules/core/24-host"
	testkeeper "github.com/cosmos/interchain-security/testutil/keeper"

	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"
)

func TestInitGenesis(t *testing.T) {

	// create a provider chain genesis manually
	consumerChainID := "consumer"
	consumerChainID2 := "consumer2"

	expClientID := "tendermint-07"
	expChannelID := "channel-0"

	expHeight := uint64(5)
	expVSCID := uint64(1)
	expTimestamp := time.Now().UTC().Add(time.Hour)
	expAddProp := types.ConsumerAdditionProposal{
		ChainId:   consumerChainID,
		SpawnTime: expTimestamp,
	}
	expRemProp := types.ConsumerRemovalProposal{
		ChainId:  consumerChainID,
		StopTime: expTimestamp,
	}
	expUbdIndex := []uint64{0, 1, 2}
	expUbdOp := ccv.UnbondingOp{
		Id:                      expVSCID,
		UnbondingConsumerChains: []string{consumerChainID},
	}
	expVSCPackets := []ccv.ValidatorSetChangePacketData{{ValsetUpdateId: expVSCID}}

	expSlashAcks := []string{sdk.ConsAddress(ed25519.GenPrivKey().PubKey().Address()).String()}
	params := providertypes.DefaultParams()

	// create genesis struct
	genesis := providertypes.NewGenesisState(expVSCID,
		[]providertypes.ValsetUpdateIdToHeight{{ValsetUpdateId: expVSCID, Height: expHeight}},
		[]providertypes.ConsumerState{
			{
				ChainId:                consumerChainID,
				ClientId:               expClientID,
				ChannelId:              expChannelID,
				InitialHeight:          expHeight,
				LockUnbondingOnTimeout: true,
				SlashDowntimeAck:       expSlashAcks,
				UnbondingOpsIndex: []providertypes.UnbondingOpIndex{
					{ValsetUpdateId: expVSCID, UnbondingOpIndex: expUbdIndex},
				},
				ConsumerGenesis: *consumertypes.DefaultGenesisState(),
			}, {
				ChainId:              consumerChainID2,
				ClientId:             expClientID,
				PendingValsetChanges: expVSCPackets,
				ConsumerGenesis:      *consumertypes.DefaultGenesisState(),
			},
		},
		[]ccv.UnbondingOp{expUbdOp},
		&ccv.MaturedUnbondingOps{Ids: expUbdIndex},
		[]providertypes.ConsumerAdditionProposal{expAddProp},
		[]providertypes.ConsumerRemovalProposal{expRemProp},
		params,
	)

	// Instantiate in-mem provider keeper with mocks
	ctrl := gomock.NewController(t)
	defer ctrl.Finish()

	keeperParams := testkeeper.NewInMemKeeperParams(t)
	mocks := testkeeper.NewMockedKeepers(ctrl)
	ctx := keeperParams.Ctx
	pk := testkeeper.NewInMemProviderKeeper(keeperParams, mocks)

	gomock.InOrder(
		mocks.MockScopedKeeper.EXPECT().GetCapability(
			ctx, host.PortPath(ccv.ProviderPortID),
		).Return(nil, true).Times(1),
	)

	// init provideer chain using genesis
	pk.InitGenesis(ctx, genesis)

	ubdOps, found := pk.GetUnbondingOp(ctx, expVSCID)
	require.True(t, found)
	require.Equal(t, expUbdOp, ubdOps)

	matureUbdOps, err := pk.GetMaturedUnbondingOps(ctx)
	require.NoError(t, err)
	require.Equal(t, expUbdIndex, matureUbdOps)

	// verify the provider chain states
	initHeight, found := pk.GetInitChainHeight(ctx, consumerChainID)
	require.True(t, found)
	require.Equal(t, expHeight, initHeight)
	channelID, found := pk.GetChainToChannel(ctx, consumerChainID)
	require.True(t, found)
	require.Equal(t, expChannelID, channelID)
	_, found = pk.GetChannelToChain(ctx, expChannelID)
	require.True(t, found)
	_, found = pk.GetConsumerClientId(ctx, consumerChainID)
	require.True(t, found)
	_, found = pk.GetConsumerClientId(ctx, consumerChainID2)
	require.True(t, found)
	vscID := pk.GetValidatorSetUpdateId(ctx)
	require.Equal(t, expVSCID, vscID)

	height, found := pk.GetValsetUpdateBlockHeight(ctx, expVSCID)
	require.True(t, found)
	require.Equal(t, expHeight, height)

	ubdIndex, found := pk.GetUnbondingOpIndex(ctx, consumerChainID, expVSCID)
	require.True(t, found)
	require.Equal(t, expUbdIndex, ubdIndex)

	addProp := pk.GetPendingConsumerAdditionProp(ctx, expTimestamp, consumerChainID)
	require.Equal(t, expAddProp, addProp)
	require.True(t, pk.GetPendingConsumerRemovalProp(ctx, consumerChainID, expTimestamp))

	pVSCPacket, found := pk.GetPendingVSCs(ctx, consumerChainID2)
	require.True(t, found)
	require.Equal(t, expVSCPackets, pVSCPacket)

	gen, found := pk.GetConsumerGenesis(ctx, consumerChainID)
	require.True(t, found)
	require.Equal(t, *consumertypes.DefaultGenesisState(), gen)

	gen2, found := pk.GetConsumerGenesis(ctx, consumerChainID2)
	require.True(t, found)
	require.Equal(t, *consumertypes.DefaultGenesisState(), gen2)

	require.Equal(t, genesis.Params, pk.GetParams(ctx))
}

func TestExportGenesis(t *testing.T) {
	pk, ctx, ctrl := testkeeper.GetProviderKeeperAndCtx(t)
	defer ctrl.Finish()

	// populate the provider states manually

	// consumer chain related states
	consumerChainID := "consumer"
	consumerChainID2 := "consumer2"
	expClientID := "tendermint-07"
	expChannelID := "channel-0"
	pk.SetConsumerClientId(ctx, consumerChainID, expClientID)
	pk.SetConsumerClientId(ctx, consumerChainID2, expClientID)
	pk.SetChainToChannel(ctx, consumerChainID, expChannelID)
	require.NoError(t, pk.SetConsumerGenesis(ctx, consumerChainID, *consumertypes.DefaultGenesisState()))
	require.NoError(t, pk.SetConsumerGenesis(ctx, consumerChainID2, *consumertypes.DefaultGenesisState()))
	pk.SetLockUnbondingOnTimeout(ctx, consumerChainID)

	// unbonding operations states
	expVSCID := uint64(1)
	expUbdOp := ccv.UnbondingOp{Id: expVSCID, UnbondingConsumerChains: []string{consumerChainID}}
	expUbdIndex := []uint64{0, 1, 2}
	pk.SetValidatorSetUpdateId(ctx, uint64(1))
	require.NoError(t, pk.SetUnbondingOp(ctx, expUbdOp))
	pk.SetUnbondingOpIndex(ctx, consumerChainID, expVSCID, expUbdIndex)
	require.NoError(t, pk.AppendMaturedUnbondingOps(ctx, expUbdIndex))

	// pending consumer chain proposals
	expTimestamp := time.Now().UTC().Add(time.Hour)
	expAddProp := types.ConsumerAdditionProposal{ChainId: consumerChainID, SpawnTime: expTimestamp}
	expRemProp := types.ConsumerRemovalProposal{ChainId: consumerChainID, StopTime: expTimestamp}
	require.NoError(t, pk.SetPendingConsumerAdditionProp(ctx, &expAddProp))
	pk.SetPendingConsumerRemovalProp(ctx, consumerChainID, expTimestamp)

	// pending VSCPacket state
	expVSCPackets := []ccv.ValidatorSetChangePacketData{{ValsetUpdateId: expVSCID}}
	pk.AppendPendingVSC(ctx, consumerChainID2, expVSCPackets[0])

	// slash acks state
	expSlashAcks := []string{sdk.ConsAddress(ed25519.GenPrivKey().PubKey().Address()).String()}
	pk.SetSlashAcks(ctx, consumerChainID, expSlashAcks)

	params := providertypes.DefaultParams()
	pk.SetParams(ctx, params)

	// create a genesis using the same provider chain states
	expGenesis := providertypes.NewGenesisState(uint64(1), []providertypes.ValsetUpdateIdToHeight{},
		[]providertypes.ConsumerState{
			{
				ChainId:                consumerChainID,
				ClientId:               expClientID,
				ChannelId:              expChannelID,
				LockUnbondingOnTimeout: true,
				SlashDowntimeAck:       expSlashAcks,
				UnbondingOpsIndex: []providertypes.UnbondingOpIndex{
					{ValsetUpdateId: expVSCID, UnbondingOpIndex: expUbdIndex},
				},
				ConsumerGenesis: *consumertypes.DefaultGenesisState(),
			}, {
				ChainId:              consumerChainID2,
				PendingValsetChanges: expVSCPackets,
				ClientId:             expClientID,
				ConsumerGenesis:      *consumertypes.DefaultGenesisState(),
			},
		},
		[]ccv.UnbondingOp{expUbdOp},
		&ccv.MaturedUnbondingOps{Ids: expUbdIndex},
		[]providertypes.ConsumerAdditionProposal{expAddProp},
		[]providertypes.ConsumerRemovalProposal{expRemProp},
		params,
	)

	// check the exported genesis
	require.Equal(t, expGenesis, pk.ExportGenesis(ctx))
}
