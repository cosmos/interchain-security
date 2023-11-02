package main

import (
	"encoding/json"
	"log"
	"testing"
	"time"

	abcitypes "github.com/cometbft/cometbft/abci/types"
	cmtproto "github.com/cometbft/cometbft/proto/tendermint/types"
	"github.com/cometbft/cometbft/types"
	cmttypes "github.com/cometbft/cometbft/types"
	"github.com/cosmos/cosmos-sdk/baseapp"
	codectypes "github.com/cosmos/cosmos-sdk/codec/types"
	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	"github.com/cosmos/cosmos-sdk/crypto/keys/secp256k1"
	sdk "github.com/cosmos/cosmos-sdk/types"
	icstestingutils "github.com/cosmos/interchain-security/v3/testutil/ibc_testing"
	"github.com/cosmos/interchain-security/v3/testutil/integration"
	"github.com/informalsystems/itf-go/itf"

	authtypes "github.com/cosmos/cosmos-sdk/x/auth/types"
	banktypes "github.com/cosmos/cosmos-sdk/x/bank/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
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

// Given a map from node names to voting powers, create a validator set with the right voting powers.
// All nodes should be included in the voting power map, even if they have voting power 0.
// This way, the nodes will have validators (that can later be assigned voting powers) and signers created for them.
//
// Returns:
// - a validator set
// - a map from node names to validator objects and
// - a map from validator addresses to private validators (signers)
func CreateValSet(t *testing.T, initialValidatorSet map[string]int64) (*cmttypes.ValidatorSet, map[string]*cmttypes.Validator, map[string]cmttypes.PrivValidator) {
	// create a valSet and signers, but the voting powers will not yet be right
	valSet, _, signers := integration.CreateValidators(t, len(initialValidatorSet))

	// create a map from validator names to validators
	valMap := make(map[string]*cmttypes.Validator)

	// impose an order on the validators
	valNames := make([]string, 0, len(initialValidatorSet))
	for valName := range initialValidatorSet {
		valNames = append(valNames, valName)
	}

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
	return valSet, valMap, signers
}

func TestItfTrace(t *testing.T) {
	path := "trace.json"
	t.Logf("🟡 Testing trace %s", path)

	// Load trace
	trace := &itf.Trace{}
	if err := trace.LoadFromFile(path); err != nil {
		log.Fatalf("Error loading trace file: %s", err)
	}

	if trace.Vars[0] != "currentState" ||
		trace.Vars[1] != "params" ||
		trace.Vars[2] != "trace" {
		t.Fatalf("Error loading trace file %s: Variables should be currentState, params, trace but are %s",
			path, trace.Vars)
	}

	t.Log("Reading params...")
	params := trace.States[0].VarValues["params"].Value.(itf.MapExprType)

	consumersExpr := params["ConsumerChains"].Value.(itf.ListExprType)
	initialValSetExpr := params["InitialValidatorSet"].Value.(itf.MapExprType)

	initialValSet := make(map[string]int64)
	for val, power := range initialValSetExpr {
		initialValSet[val] = power.Value.(int64)
	}

	consumers := make([]string, len(consumersExpr))
	for i, chain := range consumersExpr {
		consumers[i] = chain.Value.(string)
	}

	t.Log("Consumer chains are: ", consumers)

	valExprs := params["Nodes"].Value.(itf.ListExprType)
	valNames := make([]string, len(valExprs))
	for i, val := range valExprs {
		valNames[i] = val.Value.(string)
	}

	// dummyValSet is a valSet with the right validators, but not yet right powers
	valSet, addressMap, signers := CreateValSet(t, initialValSet)
	t.Log("Initial validator set is: ", valSet)
	t.Log(addressMap)
	t.Log(signers)

	// get a slice of validators in the right order
	nodes := make([]*cmttypes.Validator, len(valNames))
	for i, valName := range valNames {
		nodes[i] = addressMap[valName]
	}

	initValUpdates := types.TM2PB.ValidatorUpdates(valSet)

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
	}

	t.Log("Started chains")

	// initializing the provider chain

	t.Log("Reading the trace...")

	for index, state := range trace.States {
		t.Logf("Reading state %v", index)

		// modelState := state.VarValues["currentState"]
		trace := state.VarValues["trace"].Value.(itf.ListExprType)
		// fmt.Println(modelState)
		lastAction := trace[len(trace)-1].Value.(itf.MapExprType)

		actionKind := lastAction["kind"].Value.(string)
		switch actionKind {
		case "init":
			// start the chain(s)
		case "VotingPowerChange":
			node := lastAction["validator"].Value.(string)
			newVotingPower := lastAction["newVotingPower"].Value.(int64)
			t.Logf("Setting provider voting power of %v to %v", node, newVotingPower)

		case "EndAndBeginBlockForProvider":
			timeAdvancement := lastAction["timeAdvancement"].Value.(int64)
			consumersToStart := lastAction["consumersToStart"].Value.(itf.ListExprType)
			consumersToStop := lastAction["consumersToStop"].Value.(itf.ListExprType)
			t.Log(timeAdvancement, consumersToStart, consumersToStop)
		case "EndAndBeginBlockForConsumer":
			consumerChain := lastAction["consumerChain"].Value.(string)
			timeAdvancement := lastAction["timeAdvancement"].Value.(int64)

			t.Log(consumerChain, timeAdvancement)
		case "DeliverVscPacket":
			consumerChain := lastAction["consumerChain"].Value.(string)

			t.Log(consumerChain)
		case "DeliverVscMaturedPacket":
			consumerChain := lastAction["consumerChain"].Value.(string)

			t.Log(consumerChain)
		default:

			log.Fatalf("Error loading trace file %s, step %v: do not know action type %s",
				path, index, actionKind)
		}
	}
	t.FailNow()
}
