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
	icstestingutils "github.com/cosmos/interchain-security/v3/testutil/ibc_testing"
	simibc "github.com/cosmos/interchain-security/v3/testutil/simibc"

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

	coord.CommitBlock(chain)

	return chain
}

// Creates a path for cross-chain validation from the consumer to the provider and configures the channel config of the endpoints
// as well as the clients
func ConfigureNewPath(consumerChain *ibctesting.TestChain, providerChain *ibctesting.TestChain) *ibctesting.Path {
	path := ibctesting.NewPath(consumerChain, providerChain)
	consumerEndPoint := path.EndpointA
	providerEndPoint := path.EndpointB
	consumerEndPoint.ChannelConfig.PortID = ccvtypes.ConsumerPortID
	providerEndPoint.ChannelConfig.PortID = ccvtypes.ProviderPortID
	consumerEndPoint.ChannelConfig.Version = ccvtypes.Version
	providerEndPoint.ChannelConfig.Version = ccvtypes.Version
	consumerEndPoint.ChannelConfig.Order = channeltypes.ORDERED
	providerEndPoint.ChannelConfig.Order = channeltypes.ORDERED

	// Configure and create the consumer Client
	tmCfg := providerEndPoint.ClientConfig.(*ibctesting.TendermintConfig)
	tmCfg.UnbondingPeriod = b.initState.UnbondingC
	tmCfg.TrustingPeriod = b.initState.Trusting
	err := b.providerEndpoint().CreateClient()
	b.suite.Require().NoError(err)
	// Create the Consumer chain ID mapping in the provider state
	b.providerKeeper().SetConsumerClientId(b.providerCtx(), b.consumer().ChainID, b.providerEndpoint().ClientID)

	return path
}

func SetupChains(t *testing.T,
	s *CoreSuite,
	valSet *cmttypes.ValidatorSet, // the initial validator set
	signers map[string]cmttypes.PrivValidator, // a map of validator addresses to private validators (signers)
	nodes []*cmttypes.Validator, // the list of nodes, even ones that have no voting power initially
	consumers []string, // a list of consumer chain names
) {
	initValUpdates := cmttypes.TM2PB.ValidatorUpdates(valSet)

	t.Log("Creating coordinator")
	coordinator := ibctesting.NewCoordinator(t, 0) // start without chains, which we add later

	// start provider
	t.Log("Creating provider chain")
	providerChain := newChain(t, coordinator, icstestingutils.ProviderAppIniter, "provider", valSet, signers, nodes)
	coordinator.Chains["provider"] = providerChain

	// start consumer chains
	for _, chain := range consumers {
		t.Logf("Creating consumer chain %v", chain)
		consumerChain := newChain(t, coordinator, icstestingutils.ConsumerAppIniter(initValUpdates), chain, valSet, signers, nodes)
		coordinator.Chains[chain] = consumerChain

		path := ConfigureNewPath(consumerChain, providerChain)
	}

	// Create a client for the provider chain to use, using ibc go testing.
	b.createProvidersLocalClient()

	// Manually create a client for the consumer chain to and bootstrap
	// via genesis.
	clientState := b.createConsumersLocalClientGenesis()

	consumerGenesis := b.createConsumerGenesis(clientState)

	b.consumerKeeper().InitGenesis(b.consumerCtx(), consumerGenesis)

	// Client ID is set in InitGenesis and we treat it as a block box. So
	// must query it to use it with the endpoint.
	clientID, _ := b.consumerKeeper().GetProviderClientID(b.consumerCtx())
	b.consumerEndpoint().ClientID = clientID

	// Handshake
	b.coordinator.CreateConnections(b.path)
	b.coordinator.CreateChannels(b.path)

	// Usually the consumer sets the channel ID when it receives a first VSC packet
	// to the provider. For testing purposes, we can set it here. This is because
	// we model a blank slate: a provider and consumer that have fully established
	// their channel, and are ready for anything to happen.
	b.consumerKeeper().SetProviderChannel(b.consumerCtx(), b.consumerEndpoint().ChannelID)

	// Catch up consumer height to provider height. The provider was one ahead
	// from committing additional validators.
	simibc.EndBlock(b.consumer(), func() {})

	simibc.BeginBlock(b.consumer(), initState.BlockInterval)
	simibc.BeginBlock(b.provider(), initState.BlockInterval)

	// Commit a block on both chains, giving us two committed headers from
	// the same time and height. This is the starting point for all our
	// data driven testing.
	lastProviderHeader, _ := simibc.EndBlock(b.provider(), func() {})
	lastConsumerHeader, _ := simibc.EndBlock(b.consumer(), func() {})

	// Want the height and time of last COMMITTED block
	heightLastCommitted = b.provider().CurrentHeader.Height
	timeLastCommitted = b.provider().CurrentHeader.Time.Unix()

	// Get ready to update clients.
	simibc.BeginBlock(b.provider(), initState.BlockInterval)
	simibc.BeginBlock(b.consumer(), initState.BlockInterval)

	// Update clients to the latest header. Now everything is ready to go!
	// Ignore errors for brevity. Everything is checked in Assuptions test.
	_ = simibc.UpdateReceiverClient(b.consumerEndpoint(), b.providerEndpoint(), lastConsumerHeader)
	_ = simibc.UpdateReceiverClient(b.providerEndpoint(), b.consumerEndpoint(), lastProviderHeader)

	return b.path, b.valAddresses, heightLastCommitted, timeLastCommitted
}
