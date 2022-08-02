package keeper_test

import (
	"time"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"
	sdk "github.com/cosmos/cosmos-sdk/types"
	appProvider "github.com/cosmos/interchain-security/app/provider"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
	abci "github.com/tendermint/tendermint/abci/types"
)

func (s *KeeperTestSuite) TestGenesis() {

	// vars
	var channelID string
	var pd ccv.ValidatorSetChangePacketData
	var ts time.Time
	consumerChainID := s.consumerChain.ChainID
	vscID := uint64(1)
	ubdOp := ccv.UnbondingOp{Id: vscID, UnbondingConsumerChains: []string{consumerChainID}}
	ubdIndex := []uint64{0, 1, 2}
	var found bool

	acks := []string{sdk.ConsAddress(ed25519.GenPrivKey().PubKey().Address()).String()}

	testCases := []struct {
		name                string
		malleate            func(*KeeperTestSuite)
		assertExportGenesis func(*KeeperTestSuite, *types.GenesisState)
		assertInitGenesis   func(*KeeperTestSuite, *types.GenesisState)
	}{
		{
			name: "restart provider chain with consumer chain channel not established",
			malleate: func(s *KeeperTestSuite) {
				// channel not established
				ctx := s.providerChain.GetContext()
				pk1, err := cryptocodec.ToTmProtoPublicKey(ed25519.GenPrivKey().PubKey())
				s.Require().NoError(err)
				pd = ccv.NewValidatorSetChangePacketData(
					[]abci.ValidatorUpdate{
						{
							PubKey: pk1,
							Power:  30,
						},
					},
					1,
					nil,
				)
				s.providerChain.App.(*appProvider.App).ProviderKeeper.AppendPendingVSC(ctx, consumerChainID, pd)

			},
			assertExportGenesis: func(s *KeeperTestSuite, genesis *types.GenesisState) {
				s.Require().NotZero(genesis.ConsumerStates[0].PendingValsetChanges)
				s.Require().Equal(ccv.ValidatorSetChangePacketData{ValidatorUpdates: pd.ValidatorUpdates, ValsetUpdateId: vscID},
					genesis.ConsumerStates[0].PendingValsetChanges[0],
				)
			},
			assertInitGenesis: func(s *KeeperTestSuite, genesis *types.GenesisState) {
				ctx := s.providerChain.GetContext()

				gotPd, found := s.providerChain.App.(*appProvider.App).ProviderKeeper.GetPendingVSCs(ctx, consumerChainID)
				s.Require().True(found)
				s.Require().Equal(pd, gotPd[0])
			},
		},
		{
			name: "restart provider chain with  consumer chain channel established",
			malleate: func(s *KeeperTestSuite) {
				s.SetupCCVChannel()

				ctx := s.providerChain.GetContext()
				channelID, found = s.providerChain.App.(*appProvider.App).ProviderKeeper.GetChainToChannel(ctx, consumerChainID)
				s.Require().True(found)

				s.providerChain.App.(*appProvider.App).ProviderKeeper.SetUnbondingOp(ctx, ubdOp)
				s.providerChain.App.(*appProvider.App).ProviderKeeper.SetUnbondingOpIndex(ctx, consumerChainID, vscID, ubdIndex)

				ts = time.Now().UTC().Add(time.Hour)

				cccp := &types.CreateConsumerChainProposal{
					ChainId:   consumerChainID,
					SpawnTime: ts,
				}
				s.providerChain.App.(*appProvider.App).ProviderKeeper.SetPendingCreateProposal(ctx, cccp)
				s.providerChain.App.(*appProvider.App).ProviderKeeper.SetPendingStopProposal(ctx, consumerChainID, ts)
				s.providerChain.App.(*appProvider.App).ProviderKeeper.SetSlashAcks(ctx, consumerChainID, acks)
			},
			assertExportGenesis: func(s *KeeperTestSuite, genesis *types.GenesisState) {
				ctx := s.providerChain.GetContext()
				// check provider states

				// check consumer states
				s.Require().NotZero(genesis.ConsumerStates)
				s.Require().Equal(consumerChainID, genesis.ConsumerStates[0].ChainId)
				s.Require().Equal(channelID, genesis.ConsumerStates[0].ChannelId)

				clientID, found := s.providerChain.App.(*appProvider.App).ProviderKeeper.GetConsumerClientId(ctx, consumerChainID)
				s.Require().True(found)
				s.Require().Equal(clientID, genesis.ConsumerStates[0].ClientId)
				cGen, found := s.providerChain.App.(*appProvider.App).ProviderKeeper.GetConsumerGenesis(ctx, consumerChainID)
				s.Require().True(found)
				s.Require().Equal(cGen, genesis.ConsumerStates[0].ConsumerGenesis)

				lockUbd := s.providerChain.App.(*appProvider.App).ProviderKeeper.GetLockUnbondingOnTimeout(ctx, consumerChainID)
				s.Require().Equal(lockUbd, genesis.ConsumerStates[0].LockUnbondingOnTimeout)

				InitialHeight := s.providerChain.App.(*appProvider.App).ProviderKeeper.GetInitChainHeight(ctx, consumerChainID)
				s.Require().Equal(InitialHeight, genesis.ConsumerStates[0].InitialHeight)
				s.Require().Equal(acks, genesis.ConsumerStates[0].SlashDowntimeAck)
			},
			assertInitGenesis: func(s *KeeperTestSuite, genesis *types.GenesisState) {
				ctx := s.providerChain.GetContext()
				initHeight := s.providerChain.App.(*appProvider.App).ProviderKeeper.GetInitChainHeight(ctx, consumerChainID)
				s.Require().NotZero(initHeight)
				channelID, found := s.providerChain.App.(*appProvider.App).ProviderKeeper.GetChainToChannel(ctx, consumerChainID)
				s.Require().True(found)
				_, found = s.providerChain.App.(*appProvider.App).ProviderKeeper.GetChannelToChain(ctx, channelID)
				s.Require().True(found)
				_, found = s.providerChain.App.(*appProvider.App).ProviderKeeper.GetConsumerClientId(ctx, consumerChainID)
				s.Require().True(found)
				vscID := s.providerChain.App.(*appProvider.App).ProviderKeeper.GetValidatorSetUpdateId(ctx)
				s.Require().NotZero(vscID)
				height := s.providerChain.App.(*appProvider.App).ProviderKeeper.GetValsetUpdateBlockHeight(ctx, vscID)
				s.Require().NotZero(height)
				cccp := s.providerChain.App.(*appProvider.App).ProviderKeeper.GetPendingClientInfo(ctx, ts, consumerChainID)
				s.Require().NotZero(cccp)
				sccp := s.providerChain.App.(*appProvider.App).ProviderKeeper.GetPendingStopProposal(ctx, consumerChainID, ts)
				s.Require().NotZero(sccp)
			},
		},
	}

	for _, tc := range testCases {
		s.Run(tc.name, func() {
			tc.malleate(s)
			genesis := s.providerChain.App.(*appProvider.App).ProviderKeeper.ExportGenesis(s.providerChain.GetContext())

			tc.assertExportGenesis(s, genesis)

			s.SetupTest()

			s.Require().NotPanics(func() {
				s.providerChain.App.(*appProvider.App).ProviderKeeper.InitGenesis(s.providerChain.GetContext(), genesis)
			})

			tc.assertInitGenesis(s, genesis)
		})
	}

}
