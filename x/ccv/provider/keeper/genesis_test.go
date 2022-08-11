package keeper_test

import (
	"fmt"
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

	var (
		channelID       string
		consumerChainID string = s.consumerChain.ChainID
		restartHeight   uint64
		expVSCID        uint64
		expTimestamp    time.Time
		expPendingVSC   ccv.ValidatorSetChangePacketData
		expUbdOp        ccv.UnbondingOp
		expCreateProp   *types.CreateConsumerChainProposal
		expUbdIndex     []uint64 = []uint64{0, 1, 2}
		expSlashAcks             = []string{
			sdk.ConsAddress(ed25519.GenPrivKey().PubKey().Address()).String(),
		}
	)

	testCases := []struct {
		name                string
		malleate            func(*KeeperTestSuite)
		assertExportGenesis func(*KeeperTestSuite, *types.GenesisState)
		assertInitGenesis   func(*KeeperTestSuite, *types.GenesisState)
	}{

		{
			name: "restart provider chain with consumer chain channel established",
			malleate: func(s *KeeperTestSuite) {
				s.SetupCCVChannel()
				ctx := s.providerChain.GetContext()

				// set the provider states to export in genesis
				restartHeight = uint64(ctx.BlockHeight())
				expVSCID = s.providerChain.App.(*appProvider.App).ProviderKeeper.GetValidatorSetUpdateId(ctx)
				expTimestamp = time.Now().Add(time.Hour)
				expCreateProp = &types.CreateConsumerChainProposal{
					ChainId:   consumerChainID,
					SpawnTime: expTimestamp,
				}
				expUbdOp = ccv.UnbondingOp{
					Id:                      expVSCID,
					UnbondingConsumerChains: []string{consumerChainID},
				}

				s.providerChain.App.(*appProvider.App).ProviderKeeper.SetUnbondingOp(ctx, expUbdOp)
				s.providerChain.App.(*appProvider.App).ProviderKeeper.SetUnbondingOpIndex(ctx, consumerChainID, expVSCID, expUbdIndex)

				s.providerChain.App.(*appProvider.App).ProviderKeeper.SetLockUnbondingOnTimeout(ctx, consumerChainID)
				s.providerChain.App.(*appProvider.App).ProviderKeeper.SetPendingCreateProposal(ctx, expCreateProp)
				s.providerChain.App.(*appProvider.App).ProviderKeeper.SetPendingStopProposal(ctx, consumerChainID, expTimestamp)
				s.providerChain.App.(*appProvider.App).ProviderKeeper.SetSlashAcks(ctx, consumerChainID, expSlashAcks)
			},
			assertExportGenesis: func(s *KeeperTestSuite, genesis *types.GenesisState) {
				ctx := s.providerChain.GetContext()

				// check provider states
				s.Require().Equal(expVSCID, genesis.ValsetUpdateId)

				s.Require().Equal(restartHeight, genesis.ValsetUpdateIdToHeight[len(genesis.ValsetUpdateIdToHeight)-1].Height)
				s.Require().Equal(expVSCID-1, genesis.ValsetUpdateIdToHeight[len(genesis.ValsetUpdateIdToHeight)-1].ValsetUpdateId)
				s.Require().NotZero(genesis.UnbondingOps[0])
				s.Require().Equal(expUbdOp, genesis.UnbondingOps[0])
				fmt.Println(expUbdOp)
				s.Require().NotZero(genesis.StopConsumerChainProposals[0])
				s.Require().True(expTimestamp.UTC().Equal(genesis.StopConsumerChainProposals[0].StopTime))
				s.Require().Equal(consumerChainID, genesis.StopConsumerChainProposals[0].ChainId)

				s.Require().NotZero(genesis.CreateConsumerChainProposals[0])
				s.Require().True(expTimestamp.UTC().Equal(genesis.CreateConsumerChainProposals[0].SpawnTime))
				s.Require().Equal(consumerChainID, genesis.CreateConsumerChainProposals[0].ChainId)
				s.Require().Equal(s.providerChain.App.(*appProvider.App).ProviderKeeper.GetParams(ctx), genesis.Params)

				// check consumer states
				s.Require().NotZero(genesis.ConsumerStates)
				cs := genesis.ConsumerStates[0]
				var found bool
				channelID, found = s.providerChain.App.(*appProvider.App).ProviderKeeper.GetChainToChannel(ctx, consumerChainID)
				s.Require().True(found)
				s.Require().Equal(channelID, cs.ChannelId)

				s.Require().Equal(consumerChainID, cs.ChainId)

				clientID, found := s.providerChain.App.(*appProvider.App).ProviderKeeper.GetConsumerClientId(ctx, consumerChainID)
				s.Require().True(found)
				s.Require().Equal(clientID, cs.ClientId)
				cGen, found := s.providerChain.App.(*appProvider.App).ProviderKeeper.GetConsumerGenesis(ctx, consumerChainID)
				s.Require().True(found)
				s.Require().Equal(cGen, cs.ConsumerGenesis)

				lockUbd := s.providerChain.App.(*appProvider.App).ProviderKeeper.GetLockUnbondingOnTimeout(ctx, consumerChainID)
				s.Require().Equal(lockUbd, cs.LockUnbondingOnTimeout)

				InitialHeight := s.providerChain.App.(*appProvider.App).ProviderKeeper.GetInitChainHeight(ctx, consumerChainID)
				s.Require().Equal(InitialHeight, cs.InitialHeight)
				s.Require().Equal(expSlashAcks, cs.SlashDowntimeAck)
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
				gotVSCID := s.providerChain.App.(*appProvider.App).ProviderKeeper.GetValidatorSetUpdateId(ctx)
				s.Require().Equal(expVSCID, gotVSCID)
				height := s.providerChain.App.(*appProvider.App).ProviderKeeper.GetValsetUpdateBlockHeight(ctx, expVSCID)
				s.Require().NotZero(height)
				expCreateProp := s.providerChain.App.(*appProvider.App).ProviderKeeper.GetPendingCreateProposal(ctx, expTimestamp, consumerChainID)
				s.Require().NotZero(expCreateProp)
				sccp := s.providerChain.App.(*appProvider.App).ProviderKeeper.GetPendingStopProposal(ctx, consumerChainID, expTimestamp)
				s.Require().NotZero(sccp)
				s.Require().Equal(genesis.Params, s.providerChain.App.(*appProvider.App).ProviderKeeper.GetParams(ctx))

			},
		},
		{
			name: "restart provider chain with consumer chain channel established",
			malleate: func(s *KeeperTestSuite) {
				s.SetupTest()
				// channel not established
				ctx := s.providerChain.GetContext()
				pk1, err := cryptocodec.ToTmProtoPublicKey(ed25519.GenPrivKey().PubKey())
				s.Require().NoError(err)
				expPendingVSC = ccv.NewValidatorSetChangePacketData(
					[]abci.ValidatorUpdate{
						{
							PubKey: pk1,
							Power:  30,
						},
					},
					1,
					nil,
				)
				s.providerChain.App.(*appProvider.App).ProviderKeeper.AppendPendingVSC(ctx, consumerChainID, expPendingVSC)
			},
			assertExportGenesis: func(s *KeeperTestSuite, genesis *types.GenesisState) {
				s.Require().NotZero(genesis.ConsumerStates)
				cs := genesis.ConsumerStates[0]
				s.Require().NotZero(cs.PendingValsetChanges)
				s.Require().Equal(expPendingVSC, cs.PendingValsetChanges[0])
			},
			assertInitGenesis: func(s *KeeperTestSuite, genesis *types.GenesisState) {
				ctx := s.providerChain.GetContext()

				gotPendingVSC, found := s.providerChain.App.(*appProvider.App).ProviderKeeper.GetPendingVSCs(ctx, consumerChainID)
				s.Require().True(found)
				s.Require().Equal(expPendingVSC, gotPendingVSC[0])
			},
		},
	}

	for _, tc := range testCases {
		s.Run(tc.name, func() {
			tc.malleate(s)
			genesis := s.providerChain.App.(*appProvider.App).ProviderKeeper.ExportGenesis(s.providerChain.GetContext())

			tc.assertExportGenesis(s, genesis)

			// reset context
			s.SetupTest()

			s.Require().NotPanics(func() {
				s.providerChain.App.(*appProvider.App).ProviderKeeper.InitGenesis(s.providerChain.GetContext(), genesis)
			})

			tc.assertInitGenesis(s, genesis)
		})
	}

}
