package main

import (
	"encoding/json"
	"log"
	"sort"
	"testing"
	"time"

	clienttypes "github.com/cosmos/ibc-go/v8/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v8/modules/core/04-channel/types"
	commitmenttypes "github.com/cosmos/ibc-go/v8/modules/core/23-commitment/types"
	ibctmtypes "github.com/cosmos/ibc-go/v8/modules/light-clients/07-tendermint"
	ibctesting "github.com/cosmos/ibc-go/v8/testing"
	"github.com/stretchr/testify/require"

	"cosmossdk.io/math"

	"github.com/cosmos/cosmos-sdk/baseapp"
	codectypes "github.com/cosmos/cosmos-sdk/codec/types"
	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	"github.com/cosmos/cosmos-sdk/crypto/keys/secp256k1"
	sdk "github.com/cosmos/cosmos-sdk/types"
	authtypes "github.com/cosmos/cosmos-sdk/x/auth/types"
	banktypes "github.com/cosmos/cosmos-sdk/x/bank/types"
	slashingtypes "github.com/cosmos/cosmos-sdk/x/slashing/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	abcitypes "github.com/cometbft/cometbft/abci/types"
	cmtproto "github.com/cometbft/cometbft/proto/tendermint/types"
	cmttypes "github.com/cometbft/cometbft/types"

	icstestingutils "github.com/cosmos/interchain-security/v5/testutil/ibc_testing"
	"github.com/cosmos/interchain-security/v5/testutil/integration"
	simibc "github.com/cosmos/interchain-security/v5/testutil/simibc"
	consumertypes "github.com/cosmos/interchain-security/v5/x/ccv/consumer/types"
	ccvtypes "github.com/cosmos/interchain-security/v5/x/ccv/types"
)

const (
	INITIAL_ACCOUNT_BALANCE = 1000000000

	// Parameters used in the staking module
	STAKING_PARAMS_MAX_ENTRIES = 10000
	STAKING_PARAMS_MAX_VALS    = 100
)

// Parameters used by CometBFT
var (
	CONSENSUS_PARAMS = cmttypes.DefaultConsensusParams()
)

// Given a map from node names to voting powers, create a validator set with the right voting powers.
// All nodes should be included in the voting power map, even if they have voting power 0.
// This way, the nodes will have validators (that can later be assigned voting powers) and signers created for them.
//
// Returns:
// - a validator set
// - a map from node names to validator objects and
// - a map from validator addresses to private validators (signers)
func CreateValSet(initialValidatorSet map[string]int64, chainId string) (*cmttypes.ValidatorSet, map[string]*cmttypes.Validator, map[string]cmttypes.PrivValidator, error) {
	// create a valSet and signers, but the voting powers will not yet be right
	valSet, _, signers, err := integration.CreateValidators(len(initialValidatorSet), chainId)
	if err != nil {
		return nil, nil, nil, err
	}

	// create a map from validator names to validators
	valMap := make(map[string]*cmttypes.Validator)

	// impose an order on the validators
	valNames := make([]string, 0, len(initialValidatorSet))
	for valName := range initialValidatorSet {
		valNames = append(valNames, valName)
	}
	// sort the names so that the order is deterministic
	sort.Strings(valNames)

	// assign the validators from the created valSet to valNames in the chosen order
	for i, valName := range valNames {
		_, val := valSet.GetByIndex(int32(i))
		valMap[valName] = val
	}

	// create a valSet that has the right voting powers
	vals := make([]*cmttypes.Validator, len(valNames))
	for index, valName := range valNames {
		_, val := valSet.GetByIndex(int32(index))
		val.VotingPower = initialValidatorSet[valName]
		vals[index] = val
	}

	// override the valSet by creating a new one with the right voting powers
	valSet = cmttypes.NewValidatorSet(vals)
	return valSet, valMap, signers, nil
}

func getAppBytesAndSenders(
	chainID string,
	modelParams ModelParams,
	app ibctesting.TestingApp,
	genesis map[string]json.RawMessage,
	initialValSet *cmttypes.ValidatorSet,
	// the list of nodes that will be created, even ones that have no voting power initially
	nodes []*cmttypes.Validator,
	valNames []string,
) ([]byte, []ibctesting.SenderAccount) {
	accounts := []authtypes.GenesisAccount{}
	balances := []banktypes.Balance{}
	senderAccounts := []ibctesting.SenderAccount{}

	// Create genesis accounts.
	for i := 0; i < len(nodes); i++ {
		pk := secp256k1.GenPrivKeyFromSecret([]byte(chainID + valNames[i]))
		acc := authtypes.NewBaseAccount(pk.PubKey().Address().Bytes(), pk.PubKey(), uint64(i), 0)

		// Give enough funds for many delegations
		bal := banktypes.Balance{
			Address: acc.GetAddress().String(),
			Coins: sdk.NewCoins(sdk.NewCoin(sdk.DefaultBondDenom,
				math.NewIntFromUint64(INITIAL_ACCOUNT_BALANCE))),
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
	sumBonded := math.NewInt(0)
	initValPowers := []abcitypes.ValidatorUpdate{}

	for i, val := range nodes {
		_, valSetVal := initialValSet.GetByAddress(val.Address.Bytes())
		var tokens math.Int
		if valSetVal == nil {
			tokens = math.NewInt(0)
		} else {
			tokens = math.NewInt(valSetVal.VotingPower)
		}

		sumBonded = sumBonded.Add(tokens)

		pk, err := cryptocodec.FromTmPubKeyInterface(val.PubKey)
		if err != nil {
			log.Panicf("error getting pubkey for val %v", val)
		}
		pkAny, err := codectypes.NewAnyWithValue(pk)
		if err != nil {
			log.Panicf("error getting pubkeyAny for val %v", val)
		}

		delShares := math.LegacyNewDec(tokens.Int64()) // as many shares as tokens

		validator := stakingtypes.Validator{
			OperatorAddress: sdk.ValAddress(val.Address).String(),
			ConsensusPubkey: pkAny,
			Jailed:          false,
			Status:          stakingtypes.Bonded,
			Tokens:          tokens,
			DelegatorShares: delShares,
			Description: stakingtypes.Description{
				Moniker: valNames[i],
			},
			UnbondingHeight:   int64(0),
			UnbondingTime:     time.Unix(0, 0).UTC(),
			Commission:        stakingtypes.NewCommission(math.LegacyZeroDec(), math.LegacyZeroDec(), math.LegacyZeroDec()),
			MinSelfDelegation: math.ZeroInt(),
		}

		stakingValidators = append(stakingValidators, validator)

		// Store delegation from the model delegator account
		delegations = append(delegations, stakingtypes.NewDelegation(senderAccounts[0].SenderAccount.GetAddress().String(), val.Address.String(), delShares))

		// add initial validator powers so consumer InitGenesis runs correctly
		pub, _ := val.ToProto()
		initValPowers = append(initValPowers, abcitypes.ValidatorUpdate{
			Power:  tokens.Int64(),
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
	genesisStaking.Params.MaxEntries = STAKING_PARAMS_MAX_ENTRIES
	genesisStaking.Params.MaxValidators = STAKING_PARAMS_MAX_VALS
	genesisStaking.Params.UnbondingTime = modelParams.UnbondingPeriodPerChain[ChainId(chainID)]
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
		Coins:   sdk.Coins{sdk.NewCoin(bondDenom, math.ZeroInt())},
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
	modelParams ModelParams,
	coord *ibctesting.Coordinator,
	appInit icstestingutils.AppIniter,
	chainID string,
	validators *cmttypes.ValidatorSet,
	signers map[string]cmttypes.PrivValidator,
	nodes []*cmttypes.Validator,
	valNames []string,
) *ibctesting.TestChain {
	t.Helper()
	app, genesis := appInit()

	baseapp.SetChainID(chainID)(app.GetBaseApp())

	stateBytes, senderAccounts := getAppBytesAndSenders(chainID, modelParams, app, genesis, validators, nodes, valNames)

	protoConsParams := CONSENSUS_PARAMS.ToProto()
	app.InitChain(
		&abcitypes.RequestInitChain{
			ChainId:         chainID,
			Validators:      cmttypes.TM2PB.ValidatorUpdates(validators),
			ConsensusParams: &protoConsParams,
			AppStateBytes:   stateBytes,
		},
	)

	app.Commit()

	app.FinalizeBlock(
		&abcitypes.RequestFinalizeBlock{
			Hash:               app.LastCommitID().Hash,
			Height:             app.LastBlockHeight() + 1,
			NextValidatorsHash: validators.Hash(),
		},
	)

	chain := &ibctesting.TestChain{
		TB:          t,
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
func (s *Driver) ConfigureNewPath(consumerChain, providerChain *ibctesting.TestChain, params ModelParams) *ibctesting.Path {
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
	tmCfg.TrustingPeriod = params.TrustingPeriodPerChain[ChainId(providerChain.ChainID)]
	tmCfg.MaxClockDrift = params.TrustingPeriodPerChain[ChainId(providerChain.ChainID)] * 5 // make the clock drift a non-issue
	err := providerEndPoint.CreateClient()
	require.NoError(s.t, err, "Error creating client on provider for chain %v", consumerChain.ChainID)

	// Create the Consumer chain ID mapping in the provider state
	s.providerKeeper().SetConsumerClientId(providerChain.GetContext(), consumerChain.ChainID, providerEndPoint.ClientID)

	// Configure and create the client on the consumer
	tmCfg = consumerEndPoint.ClientConfig.(*ibctesting.TendermintConfig)
	tmCfg.UnbondingPeriod = params.UnbondingPeriodPerChain[consumerChainId]
	tmCfg.TrustingPeriod = params.TrustingPeriodPerChain[consumerChainId]
	tmCfg.MaxClockDrift = params.TrustingPeriodPerChain[ChainId(providerChain.ChainID)] * 5 // make the clock drift a non-issue

	consumerClientState := ibctmtypes.NewClientState(
		providerChain.ChainID, tmCfg.TrustLevel, tmCfg.TrustingPeriod, tmCfg.UnbondingPeriod, tmCfg.MaxClockDrift,
		providerChain.LastHeader.GetHeight().(clienttypes.Height), commitmenttypes.GetSDKSpecs(),
		[]string{"upgrade", "upgradedIBCState"},
	)

	consumerGenesis := createConsumerGenesis(params, providerChain, consumerClientState)

	s.consumerKeeper(consumerChainId).InitGenesis(s.ctx(consumerChainId), consumerGenesis)

	consumerGenesisForProvider := ccvtypes.ConsumerGenesisState{
		Params:   consumerGenesis.Params,
		Provider: consumerGenesis.Provider,
		NewChain: consumerGenesis.NewChain,
	}

	var stakingValidators []stakingtypes.Validator

	// set up the current consumer validators by utilizing the initial validator set
	for _, val := range consumerGenesisForProvider.Provider.InitialValSet {
		pubKey := val.PubKey
		consAddr, err := ccvtypes.TMCryptoPublicKeyToConsAddr(pubKey)
		if err != nil {
			continue
		}

		v, found := s.providerStakingKeeper().GetValidatorByConsAddr(s.providerCtx(), consAddr)
		if !found {
			continue
		}
		stakingValidators = append(stakingValidators, v)
	}

	nextValidators := s.providerKeeper().ComputeNextEpochConsumerValSet(s.providerCtx(), string(consumerChainId), stakingValidators)
	s.providerKeeper().SetConsumerValSet(s.providerCtx(), string(consumerChainId), nextValidators)

	err = s.providerKeeper().SetConsumerGenesis(
		providerChain.GetContext(),
		string(consumerChainId),
		consumerGenesisForProvider)
	require.NoError(s.t, err, "Error setting consumer genesis on provider for chain %v", consumerChain.ChainID)

	// Client ID is set in InitGenesis and we treat it as a black box. So
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

	// TODO: remove if not needed
	// Commit a block on both chains, giving us two committed headers from
	// the same time and height. This is the starting point for all our
	// data driven testing.
	// lastConsumerHeader, _ := simibc.FinalizeBlock(consumerChain, 5)
	// lastProviderHeader, _ := simibc.FinalizeBlock(providerChain, 5)

	// // Update clients to the latest header.
	// err = simibc.UpdateReceiverClient(consumerEndPoint, providerEndPoint, lastConsumerHeader, false)
	// require.NoError(s.t, err, "Error updating client on consumer for chain %v", consumerChain.ChainID)
	// err = simibc.UpdateReceiverClient(providerEndPoint, consumerEndPoint, lastProviderHeader, false)
	// require.NoError(s.t, err, "Error updating client on provider for chain %v", consumerChain.ChainID)

	// path is ready to go
	return path
}

func (s *Driver) providerHeader() *ibctmtypes.Header {
	return s.coordinator.Chains["provider"].LastHeader
}

func (s *Driver) setupProvider(
	params ModelParams,
	valSet *cmttypes.ValidatorSet, // the initial validator set
	signers map[string]cmttypes.PrivValidator, // a map of validator addresses to private validators (signers)
	nodes []*cmttypes.Validator, // the list of nodes, even ones that have no voting power initially
	valNames []string,
) {
	// start provider
	s.t.Log("Creating provider chain")
	providerChain := newChain(s.t, params, s.coordinator, icstestingutils.ProviderAppIniter, "provider", valSet, signers, nodes, valNames)
	s.coordinator.Chains["provider"] = providerChain

	// set the VscTimeout
	s.providerKeeper().SetVscTimeoutPeriod(s.ctx("provider"), params.VscTimeout)
	// set the CcvTimeoutPeriod
	providerParams := s.providerKeeper().GetParams(s.ctx("provider"))
	providerParams.CcvTimeoutPeriod = params.CcvTimeout[ChainId(providerChain.ChainID)]
	providerParams.SlashMeterReplenishFraction = "1"
	providerParams.SlashMeterReplenishPeriod = time.Nanosecond
	s.providerKeeper().SetParams(s.ctx("provider"), providerParams)

	// set the signing infos
	for _, val := range nodes {
		s.providerSlashingKeeper().SetValidatorSigningInfo(s.ctx("provider"), val.Address.Bytes(), slashingtypes.ValidatorSigningInfo{
			Address:             val.Address.String(),
			StartHeight:         0,
			IndexOffset:         0,
			JailedUntil:         time.Time{},
			Tombstoned:          false,
			MissedBlocksCounter: 0,
		})
	}

	// produce a first block
	simibc.FinalizeBlock(providerChain, 0)
}

func (s *Driver) setupConsumer(
	chain string,
	params ModelParams,
	valSet *cmttypes.ValidatorSet, // the current validator set on the provider chain
	signers map[string]cmttypes.PrivValidator, // a map of validator addresses to private validators (signers)
	nodes []*cmttypes.Validator, // the list of nodes, even ones that have no voting power initially
	valNames []string,
	providerChain *ibctesting.TestChain,
) {
	s.t.Logf("Starting consumer %v", chain)

	initValUpdates := cmttypes.TM2PB.ValidatorUpdates(valSet)

	// start consumer chains
	s.t.Logf("Creating consumer chain %v", chain)
	consumerChain := newChain(s.t, params, s.coordinator, icstestingutils.ConsumerAppIniter(initValUpdates), chain, valSet, signers, nodes, valNames)
	s.coordinator.Chains[chain] = consumerChain

	path := s.ConfigureNewPath(consumerChain, providerChain, params)
	s.simibcs[ChainId(chain)] = simibc.MakeRelayedPath(s.t, path)
}

func createConsumerGenesis(modelParams ModelParams, providerChain *ibctesting.TestChain, consumerClientState *ibctmtypes.ClientState) *consumertypes.GenesisState {
	providerConsState := providerChain.LastHeader.ConsensusState()

	valUpdates := cmttypes.TM2PB.ValidatorUpdates(providerChain.Vals)
	params := ccvtypes.NewParams(
		true,
		1000, // ignore distribution
		"",   // ignore distribution
		"",   // ignore distribution
		modelParams.CcvTimeout[ChainId(consumerClientState.ChainId)],
		ccvtypes.DefaultTransferTimeoutPeriod,
		ccvtypes.DefaultConsumerRedistributeFrac,
		ccvtypes.DefaultHistoricalEntries,
		modelParams.UnbondingPeriodPerChain[ChainId(consumerClientState.ChainId)],
		"0", // disable soft opt-out
		[]string{},
		[]string{},
		ccvtypes.DefaultRetryDelayPeriod,
	)

	return consumertypes.NewInitialGenesisState(consumerClientState, providerConsState, valUpdates, params)
}
