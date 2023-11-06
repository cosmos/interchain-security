package main

import (
	"encoding/json"
	"log"
	"testing"
	"time"

	abcitypes "github.com/cometbft/cometbft/abci/types"
	cmtproto "github.com/cometbft/cometbft/proto/tendermint/types"
	cmttypes "github.com/cometbft/cometbft/types"
	"github.com/cosmos/cosmos-sdk/baseapp"
	codectypes "github.com/cosmos/cosmos-sdk/codec/types"
	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	"github.com/cosmos/cosmos-sdk/crypto/keys/secp256k1"
	sdk "github.com/cosmos/cosmos-sdk/types"
	clienttypes "github.com/cosmos/ibc-go/v7/modules/core/02-client/types"
	commitmenttypes "github.com/cosmos/ibc-go/v7/modules/core/23-commitment/types"
	ibctmtypes "github.com/cosmos/ibc-go/v7/modules/light-clients/07-tendermint"
	icstestingutils "github.com/cosmos/interchain-security/v3/testutil/ibc_testing"
	simibc "github.com/cosmos/interchain-security/v3/testutil/simibc"
	"github.com/stretchr/testify/require"

	ccv "github.com/cosmos/interchain-security/v3/x/ccv/types"

	authtypes "github.com/cosmos/cosmos-sdk/x/auth/types"
	banktypes "github.com/cosmos/cosmos-sdk/x/bank/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	channeltypes "github.com/cosmos/ibc-go/v7/modules/core/04-channel/types"
	consumertypes "github.com/cosmos/interchain-security/v3/x/ccv/consumer/types"
	ccvtypes "github.com/cosmos/interchain-security/v3/x/ccv/types"

	ibctesting "github.com/cosmos/ibc-go/v7/testing"
)

const (
	INITIAL_ACCOUNT_BALANCE = 1000000000

	// Parameters used in the staking module
	StakingParamsMaxEntries    = 10000
	StakingParamsMaxValidators = 100
	StakingParamsUnbondingTime = 5 * 7 * 24 * time.Hour // 5 weeks
)

// Parameters used by CometBFT
var (
	ConsensusParams = cmttypes.DefaultConsensusParams()
)

func getAppBytesAndSenders(
	chainID string,
	app ibctesting.TestingApp,
	genesis map[string]json.RawMessage,
	initialValSet *cmttypes.ValidatorSet,
	// the list of nodes that will be created, even ones that have no voting power initially
	nodes []*cmttypes.Validator,
) ([]byte, []ibctesting.SenderAccount) {
	accounts := []authtypes.GenesisAccount{}
	balances := []banktypes.Balance{}
	senderAccounts := []ibctesting.SenderAccount{}

	// Create genesis accounts.
	for i := 0; i < len(nodes); i++ {
		pk := secp256k1.GenPrivKey()
		acc := authtypes.NewBaseAccount(pk.PubKey().Address().Bytes(), pk.PubKey(), uint64(i), 0)

		// Give enough funds for many delegations
		// Extra units are to delegate to extra validators created later
		// in order to bond them and still have INITIAL_DELEGATOR_TOKENS remaining
		bal := banktypes.Balance{
			Address: acc.GetAddress().String(),
			Coins: sdk.NewCoins(sdk.NewCoin(sdk.DefaultBondDenom,
				sdk.NewIntFromUint64(INITIAL_ACCOUNT_BALANCE))),
		}

		accounts = append(accounts, acc)
		balances = append(balances, bal)

		senderAccount := ibctesting.SenderAccount{
			SenderAccount: acc,
			SenderPrivKey: pk,
		}

		senderAccounts = append(senderAccounts, senderAccount)
	}

	// set genesis accounts
	genesisAuth := authtypes.NewGenesisState(authtypes.DefaultParams(), accounts)
	genesis[authtypes.ModuleName] = app.AppCodec().MustMarshalJSON(genesisAuth)

	// create initial validator set and its delegations
	stakingValidators := make([]stakingtypes.Validator, 0, len(nodes))
	delegations := make([]stakingtypes.Delegation, 0, len(nodes))

	// Sum bonded is needed for BondedPool account
	sumBonded := sdk.NewInt(0)
	initValPowers := []abcitypes.ValidatorUpdate{}

	for i, val := range nodes {
		_, valSetVal := initialValSet.GetByAddress(val.Address.Bytes())
		valAccount := accounts[i]
		if valSetVal == nil {
			log.Panicf("error getting validator with address %v from valSet %v", val, initialValSet)
		}
		tokens := sdk.NewInt(valSetVal.VotingPower)
		sumBonded = sumBonded.Add(tokens)

		pk, err := cryptocodec.FromTmPubKeyInterface(val.PubKey)
		if err != nil {
			log.Panicf("error getting pubkey for val %v", val)
		}
		pkAny, err := codectypes.NewAnyWithValue(pk)
		if err != nil {
			log.Panicf("error getting pubkeyAny for val %v", val)
		}

		var valStatus stakingtypes.BondStatus
		if val.VotingPower > 0 {
			valStatus = stakingtypes.Bonded
		} else {
			valStatus = stakingtypes.Unbonded
		}

		delShares := sdk.NewDec(tokens.Int64()) // as many shares as tokens

		validator := stakingtypes.Validator{
			OperatorAddress:   sdk.ValAddress(val.Address).String(),
			ConsensusPubkey:   pkAny,
			Jailed:            false,
			Status:            valStatus,
			Tokens:            tokens,
			DelegatorShares:   delShares,
			Description:       stakingtypes.Description{},
			UnbondingHeight:   int64(0),
			UnbondingTime:     time.Unix(0, 0).UTC(),
			Commission:        stakingtypes.NewCommission(sdk.ZeroDec(), sdk.ZeroDec(), sdk.ZeroDec()),
			MinSelfDelegation: sdk.ZeroInt(),
		}

		stakingValidators = append(stakingValidators, validator)

		// Store delegation from the model delegator account
		delegations = append(delegations, stakingtypes.NewDelegation(valAccount.GetAddress(), val.Address.Bytes(), delShares))

		// add initial validator powers so consumer InitGenesis runs correctly
		pub, _ := val.ToProto()
		initValPowers = append(initValPowers, abcitypes.ValidatorUpdate{
			Power:  val.VotingPower,
			PubKey: pub.PubKey,
		})
	}

	bondDenom := sdk.DefaultBondDenom
	genesisStaking := stakingtypes.GenesisState{}
	genesisConsumer := consumertypes.GenesisState{}

	if genesis[stakingtypes.ModuleName] != nil {
		// If staking module genesis already exists
		app.AppCodec().MustUnmarshalJSON(genesis[stakingtypes.ModuleName], &genesisStaking)
		bondDenom = genesisStaking.Params.BondDenom
	}

	if genesis[ccvtypes.ModuleName] != nil {
		app.AppCodec().MustUnmarshalJSON(genesis[ccvtypes.ModuleName], &genesisConsumer)
		genesisConsumer.Provider.InitialValSet = initValPowers
		genesisConsumer.Params.Enabled = true
		genesis[ccvtypes.ModuleName] = app.AppCodec().MustMarshalJSON(&genesisConsumer)
	}

	// Set model parameters
	genesisStaking.Params.MaxEntries = StakingParamsMaxEntries
	genesisStaking.Params.MaxValidators = StakingParamsMaxValidators
	genesisStaking.Params.UnbondingTime = StakingParamsUnbondingTime
	genesisStaking = *stakingtypes.NewGenesisState(genesisStaking.Params, stakingValidators, delegations)
	genesis[stakingtypes.ModuleName] = app.AppCodec().MustMarshalJSON(&genesisStaking)

	// add bonded amount to bonded pool module account
	balances = append(balances, banktypes.Balance{
		Address: authtypes.NewModuleAddress(stakingtypes.BondedPoolName).String(),
		Coins:   sdk.Coins{sdk.NewCoin(bondDenom, sumBonded)},
	})

	// add unbonded amount
	balances = append(balances, banktypes.Balance{
		Address: authtypes.NewModuleAddress(stakingtypes.NotBondedPoolName).String(),
		Coins:   sdk.Coins{sdk.NewCoin(bondDenom, sdk.ZeroInt())},
	})

	// update total funds supply
	genesisBank := banktypes.NewGenesisState(banktypes.DefaultGenesisState().Params, balances, sdk.NewCoins(), []banktypes.Metadata{}, []banktypes.SendEnabled{})
	genesis[banktypes.ModuleName] = app.AppCodec().MustMarshalJSON(genesisBank)

	stateBytes, err := json.MarshalIndent(genesis, "", " ")
	if err != nil {
		log.Panicf("error marshalling genesis: %v", err)
	}

	return stateBytes, senderAccounts
}

func newChain(
	t *testing.T,
	coord *ibctesting.Coordinator,
	appInit icstestingutils.AppIniter,
	chainID string,
	validators *cmttypes.ValidatorSet,
	signers map[string]cmttypes.PrivValidator,
	nodes []*cmttypes.Validator,
) *ibctesting.TestChain {
	app, genesis := appInit()

	baseapp.SetChainID(chainID)(app.GetBaseApp())

	stateBytes, senderAccounts := getAppBytesAndSenders(chainID, app, genesis, validators, nodes)

	protoConsParams := ConsensusParams.ToProto()
	app.InitChain(
		abcitypes.RequestInitChain{
			ChainId:         chainID,
			Validators:      []abcitypes.ValidatorUpdate{},
			ConsensusParams: &protoConsParams,
			AppStateBytes:   stateBytes,
		},
	)

	app.Commit()

	app.BeginBlock(
		abcitypes.RequestBeginBlock{
			Header: cmtproto.Header{
				ChainID:            chainID,
				Height:             app.LastBlockHeight() + 1,
				AppHash:            app.LastCommitID().Hash,
				ValidatorsHash:     validators.Hash(),
				NextValidatorsHash: validators.Hash(),
			},
		},
	)

	chain := &ibctesting.TestChain{
		T:           t,
		Coordinator: coord,
		ChainID:     chainID,
		App:         app,
		CurrentHeader: cmtproto.Header{
			ChainID: chainID,
			Height:  1,
			Time:    coord.CurrentTime.UTC(),
		},
		QueryServer:    app.GetIBCKeeper(),
		TxConfig:       app.GetTxConfig(),
		Codec:          app.AppCodec(),
		Vals:           validators,
		NextVals:       validators,
		Signers:        signers,
		SenderPrivKey:  senderAccounts[0].SenderPrivKey,
		SenderAccount:  senderAccounts[0].SenderAccount,
		SenderAccounts: senderAccounts,
	}

	chain.NextBlock()

	return chain
}

// Creates a path for cross-chain validation from the consumer to the provider and configures the channel config of the endpoints
// as well as the clients.
// this function stops when there is an initialized, ready-to-relay channel between the provider and consumer.
func (s *Driver) ConfigureNewPath(consumerChain *ibctesting.TestChain, providerChain *ibctesting.TestChain, params ModelParams, lastProviderHeader *ibctmtypes.Header) *ibctesting.Path {
	consumerChainId := ChainId(consumerChain.ChainID)

	path := ibctesting.NewPath(consumerChain, providerChain)
	consumerEndPoint := path.EndpointA
	providerEndPoint := path.EndpointB
	consumerEndPoint.ChannelConfig.PortID = ccvtypes.ConsumerPortID
	providerEndPoint.ChannelConfig.PortID = ccvtypes.ProviderPortID
	consumerEndPoint.ChannelConfig.Version = ccvtypes.Version
	providerEndPoint.ChannelConfig.Version = ccvtypes.Version
	consumerEndPoint.ChannelConfig.Order = channeltypes.ORDERED
	providerEndPoint.ChannelConfig.Order = channeltypes.ORDERED

	// Configure and create the client on the provider
	tmCfg := providerEndPoint.ClientConfig.(*ibctesting.TendermintConfig)
	tmCfg.UnbondingPeriod = params.UnbondingPeriodPerChain[ChainId(providerChain.ChainID)]
	err := providerEndPoint.CreateClient()
	require.NoError(s.t, err, "Error creating client on provider for chain %v", consumerChain.ChainID)

	// Create the Consumer chain ID mapping in the provider state
	s.providerKeeper().SetConsumerClientId(providerChain.GetContext(), consumerChain.ChainID, providerEndPoint.ClientID)

	// Configure and create the client on the consumer
	tmCfg = consumerEndPoint.ClientConfig.(*ibctesting.TendermintConfig)
	tmCfg.UnbondingPeriod = params.UnbondingPeriodPerChain[consumerChainId]

	consumerClientState := ibctmtypes.NewClientState(
		providerChain.ChainID, tmCfg.TrustLevel, tmCfg.TrustingPeriod, tmCfg.UnbondingPeriod, tmCfg.MaxClockDrift,
		providerChain.LastHeader.GetHeight().(clienttypes.Height), commitmenttypes.GetSDKSpecs(),
		[]string{"upgrade", "upgradedIBCState"},
	)

	consumerGenesis := createConsumerGenesis(params, providerChain, consumerClientState)

	s.consumerKeeper(consumerChainId).InitGenesis(s.ctx(consumerChainId), consumerGenesis)

	// Client ID is set in InitGenesis and we treat it as a block box. So
	// must query it to use it with the endpoint.
	clientID, _ := s.consumerKeeper(consumerChainId).GetProviderClientID(s.ctx(consumerChainId))
	consumerEndPoint.ClientID = clientID

	// Handshake
	s.coordinator.CreateConnections(path)
	s.coordinator.CreateChannels(path)

	// Usually the consumer sets the channel ID when it receives a first VSC packet
	// to the provider. For testing purposes, we can set it here. This is because
	// we model a blank slate: a provider and consumer that have fully established
	// their channel, and are ready for anything to happen.
	s.consumerKeeper(consumerChainId).SetProviderChannel(s.ctx(consumerChainId), consumerEndPoint.ChannelID)

	// // Catch up consumer height to provider height. The provider was one ahead TODO: activate this
	// // from committing additional validators.
	// simibc.EndBlock(consumerChain, func() {})

	// simibc.BeginBlock(consumerChain, initState.BlockInterval)
	// simibc.BeginBlock(providerChain, initState.BlockInterval)

	// Commit a block on both chains, giving us two committed headers from
	// the same time and height. This is the starting point for all our
	// data driven testing.
	lastConsumerHeader, _ := simibc.EndBlock(consumerChain, func() {})

	// Get ready to update clients.
	simibc.BeginBlock(providerChain, 0)
	simibc.BeginBlock(consumerChain, 0)

	// Update clients to the latest header.
	err = simibc.UpdateReceiverClient(consumerEndPoint, providerEndPoint, lastConsumerHeader)
	require.NoError(s.t, err, "Error updating client on consumer for chain %v", consumerChain.ChainID)
	err = simibc.UpdateReceiverClient(providerEndPoint, consumerEndPoint, lastProviderHeader)
	require.NoError(s.t, err, "Error updating client on provider for chain %v", consumerChain.ChainID)

	// path is ready to go
	return path
}

func (s *Driver) setupChains(
	params ModelParams,
	valSet *cmttypes.ValidatorSet, // the initial validator set
	signers map[string]cmttypes.PrivValidator, // a map of validator addresses to private validators (signers)
	nodes []*cmttypes.Validator, // the list of nodes, even ones that have no voting power initially
	consumers []string, // a list of consumer chain names
) {
	initValUpdates := cmttypes.TM2PB.ValidatorUpdates(valSet)
	// start provider
	s.t.Log("Creating provider chain")
	providerChain := newChain(s.t, s.coordinator, icstestingutils.ProviderAppIniter, "provider", valSet, signers, nodes)
	s.coordinator.Chains["provider"] = providerChain

	providerHeader, _ := simibc.EndBlock(providerChain, func() {})

	// start consumer chains
	for _, chain := range consumers {
		s.t.Logf("Creating consumer chain %v", chain)
		consumerChain := newChain(s.t, s.coordinator, icstestingutils.ConsumerAppIniter(initValUpdates), chain, valSet, signers, nodes)
		s.coordinator.Chains[chain] = consumerChain

		path := s.ConfigureNewPath(consumerChain, providerChain, params, providerHeader)
		relayedPath := simibc.MakeRelayedPath(s.t, path)
		s.simibcs[ChainId(chain)] = &relayedPath
	}
}

func createConsumerGenesis(modelParams ModelParams, providerChain *ibctesting.TestChain, consumerClientState *ibctmtypes.ClientState) *consumertypes.GenesisState {
	providerConsState := providerChain.LastHeader.ConsensusState()

	valUpdates := cmttypes.TM2PB.ValidatorUpdates(providerChain.Vals)
	params := ccv.NewParams(
		true,
		1000, // ignore distribution
		"",   // ignore distribution
		"",   // ignore distribution
		ccv.DefaultCCVTimeoutPeriod,
		ccv.DefaultTransferTimeoutPeriod,
		ccv.DefaultConsumerRedistributeFrac,
		ccv.DefaultHistoricalEntries,
		consumerClientState.UnbondingPeriod,
		"0", // disable soft opt-out
		[]string{},
		[]string{},
		ccv.DefaultRetryDelayPeriod,
	)
	return consumertypes.NewInitialGenesisState(consumerClientState, providerConsState, valUpdates, params)
}
