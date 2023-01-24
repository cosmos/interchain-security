package ibc_testing

import (
	"testing"

	sdk "github.com/cosmos/cosmos-sdk/types"
	clienttypes "github.com/cosmos/ibc-go/v4/modules/core/02-client/types"
	ibctesting "github.com/cosmos/interchain-security/legacy_ibc_testing/testing"
	e2eutil "github.com/cosmos/interchain-security/testutil/e2e"
	testkeeper "github.com/cosmos/interchain-security/testutil/keeper"
	consumerkeeper "github.com/cosmos/interchain-security/x/ccv/consumer/keeper"

	"github.com/stretchr/testify/suite"

	tmencoding "github.com/tendermint/tendermint/crypto/encoding"
	tmtypes "github.com/tendermint/tendermint/types"
)

// Contains generic setup code for running e2e tests against a provider, consumer,
// and/or democracy consumer app.go implementation. You should not need to modify or replicate this file
// to run e2e tests against your app.go implementations!

var (
	FirstConsumerChainID = ibctesting.GetChainID(2)
	provChainID          = ibctesting.GetChainID(1)
	democConsumerChainID = ibctesting.GetChainID(5000)
)

// ConsumerBundle serves as a way to store useful in-mem consumer app chain state
// and relevant IBC paths in the context of CCV e2e testing.
type ConsumerBundle struct {
	Chain        *ibctesting.TestChain
	App          e2eutil.ConsumerApp
	Path         *ibctesting.Path
	TransferPath *ibctesting.Path
}

// GetCtx returns the context for the ConsumerBundle
func (cb ConsumerBundle) GetCtx() sdk.Context {
	return cb.Chain.GetContext()
}

// GetKeeper returns the keeper for the ConsumerBundle
func (cb ConsumerBundle) GetKeeper() consumerkeeper.Keeper {
	return cb.App.GetConsumerKeeper()
}

// AddProvider adds a new provider chain to the coordinator and returns the test chain and app type
func AddProvider[T e2eutil.ProviderApp](coordinator *ibctesting.Coordinator, t *testing.T, appIniter ibctesting.AppIniter) (
	*ibctesting.TestChain, T) {

	provider := ibctesting.NewTestChain(t, coordinator, appIniter, provChainID)
	coordinator.Chains[provChainID] = provider

	return provider, provider.App.(T)
}

// AddDemocracyConsumer adds a new democ consumer chain to the coordinator and returns the test chain and app type
func AddDemocracyConsumer[T e2eutil.DemocConsumerApp](coordinator *ibctesting.Coordinator, t *testing.T,
	appIniter ibctesting.AppIniter) (*ibctesting.TestChain, T) {

	democConsumer := ibctesting.NewTestChain(t, coordinator, appIniter, democConsumerChainID)
	coordinator.Chains[democConsumerChainID] = democConsumer

	return democConsumer, democConsumer.App.(T)
}

// AddConsumer adds a new consumer chain with "testchain<index+2>" as chainID to the coordinator
// and returns the test chain and app type. A new client is created on the provider to the new
// consumer chain (see CreateConsumerClient). The new consumer is initialized with the
// InitialValSet from the genesis state generated by the provider (see MakeConsumerGenesis).
//
// This method must be called after AddProvider.
func AddConsumer[Tp e2eutil.ProviderApp, Tc e2eutil.ConsumerApp](
	coordinator *ibctesting.Coordinator,
	s *suite.Suite,
	index int,
	appIniter ibctesting.AppIniter,
) *ConsumerBundle {
	// consumer chain ID
	chainID := ibctesting.GetChainID(index + 2)

	// create client to the consumer on the provider chain
	providerChain := coordinator.Chains[provChainID]
	providerApp := providerChain.App.(Tp)
	providerKeeper := providerApp.GetProviderKeeper()

	prop := testkeeper.GetTestConsumerAdditionProp()
	prop.ChainId = chainID
	// NOTE: the initial height passed to CreateConsumerClient
	// must be the height on the consumer when InitGenesis is called
	prop.InitialHeight = clienttypes.Height{RevisionNumber: 0, RevisionHeight: 3}
	err := providerKeeper.CreateConsumerClient(
		providerChain.GetContext(),
		prop,
	)
	s.Require().NoError(err)

	// commit the state on the provider chain
	coordinator.CommitBlock(providerChain)

	// get genesis state created by the provider
	consumerGenesisState, found := providerKeeper.GetConsumerGenesis(
		providerChain.GetContext(),
		chainID,
	)
	s.Require().True(found, "consumer genesis not found")

	// use InitialValSet as the valset on the consumer
	var valz []*tmtypes.Validator
	for _, update := range consumerGenesisState.InitialValSet {
		// tmPubKey update.PubKey
		tmPubKey, err := tmencoding.PubKeyFromProto(update.PubKey)
		s.Require().NoError(err)
		valz = append(valz, &tmtypes.Validator{
			PubKey:           tmPubKey,
			VotingPower:      update.Power,
			Address:          tmPubKey.Address(),
			ProposerPriority: 0,
		})
	}

	// create and instantiate consumer chain
	testChain := ibctesting.NewTestChainWithValSet(s.T(), coordinator,
		appIniter, chainID, tmtypes.NewValidatorSet(valz), providerChain.Signers)
	coordinator.Chains[chainID] = testChain

	return &ConsumerBundle{
		Chain: testChain,
		App:   testChain.App.(Tc),
	}
}
