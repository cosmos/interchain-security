package difftest

import (
	"encoding/json"
	"testing"
	"time"

	codectypes "github.com/cosmos/cosmos-sdk/codec/types"
	"github.com/cosmos/cosmos-sdk/crypto/keys/secp256k1"
	sdk "github.com/cosmos/cosmos-sdk/types"
	authtypes "github.com/cosmos/cosmos-sdk/x/auth/types"
	banktypes "github.com/cosmos/cosmos-sdk/x/bank/types"
	"github.com/stretchr/testify/require"
	abci "github.com/tendermint/tendermint/abci/types"
	tmproto "github.com/tendermint/tendermint/proto/tendermint/types"
	tmtypes "github.com/tendermint/tendermint/types"

	"github.com/cosmos/ibc-go/v3/testing/mock"

	ibctesting "github.com/cosmos/ibc-go/v3/testing"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	simapp "github.com/cosmos/interchain-security/testutil/simapp"
)

// TODO: move somewhere sensible with the other constants
const UNBONDING_P = time.Second * 70
const UNBONDING_C = time.Second * 45
const TRUSTING = time.Second * 44
const MAX_CLOCK_DRIFT = time.Second * 10000
const TOKEN_SCALAR = 10000

var DTDefaultConsensusParams = &abci.ConsensusParams{
	Block: &abci.BlockParams{
		MaxBytes: 200000,
		MaxGas:   2000000,
	},
	Evidence: &tmproto.EvidenceParams{
		MaxAgeNumBlocks: 302400,
		MaxAgeDuration:  504 * time.Hour, // 3 weeks is the max duration
		MaxBytes:        10000,
	},
	Validator: &tmproto.ValidatorParams{
		PubKeyTypes: []string{
			tmtypes.ABCIPubKeyTypeEd25519,
		},
	},
}

type InitialModelState struct {
	Delegation []int64
	Status     []stakingtypes.BondStatus
}

func DTSetupWithGenesisValSet(t *testing.T, appIniter ibctesting.AppIniter, valSet *tmtypes.ValidatorSet, genAccs []authtypes.GenesisAccount, chainID string, balances ...banktypes.Balance) ibctesting.TestingApp {
	app, genesisState := appIniter()

	// set genesis accounts
	authGenesis := authtypes.NewGenesisState(authtypes.DefaultParams(), genAccs)
	genesisState[authtypes.ModuleName] = app.AppCodec().MustMarshalJSON(authGenesis)

	validators := make([]stakingtypes.Validator, 0, len(valSet.Validators))
	delegations := make([]stakingtypes.Delegation, 0, len(valSet.Validators))

	// tokens = power
	require.Equal(t, sdk.NewInt(1), sdk.DefaultPowerReduction)
	require.Equal(t, 2, len(valSet.Validators))

	initialModelState := InitialModelState{
		Delegation: []int64{4 * TOKEN_SCALAR, 3 * TOKEN_SCALAR},
		Status:     []stakingtypes.BondStatus{stakingtypes.Bonded, stakingtypes.Bonded},
	}

	totalBonded := sdk.NewInt(0)
	totalUnbonded := sdk.NewInt(0)

	for i, val := range valSet.Validators {
		delegation := initialModelState.Delegation[i]
		status := initialModelState.Status[i]

		add := int64(1 * TOKEN_SCALAR)
		tokens := sdk.NewInt(delegation + add)
		if status == stakingtypes.Bonded {
			totalBonded = totalBonded.Add(tokens)
		}
		if status == stakingtypes.Unbonded {
			totalUnbonded = totalUnbonded.Add(tokens)
		}
		delShares := sdk.NewDec(delegation)
		shares := sdk.NewDec(delegation + add)

		pk, err := cryptocodec.FromTmPubKeyInterface(val.PubKey)
		require.NoError(t, err)
		pkAny, err := codectypes.NewAnyWithValue(pk)
		require.NoError(t, err)
		validator := stakingtypes.Validator{
			OperatorAddress:   sdk.ValAddress(val.Address).String(),
			ConsensusPubkey:   pkAny,
			Jailed:            false,
			Status:            status,
			Tokens:            tokens,
			DelegatorShares:   shares,
			Description:       stakingtypes.Description{},
			UnbondingHeight:   int64(0),
			UnbondingTime:     time.Unix(0, 0).UTC(),
			Commission:        stakingtypes.NewCommission(sdk.ZeroDec(), sdk.ZeroDec(), sdk.ZeroDec()),
			MinSelfDelegation: sdk.ZeroInt(),
		}

		validators = append(validators, validator)
		del := stakingtypes.NewDelegation(genAccs[0].GetAddress(), val.Address.Bytes(), delShares)
		delegations = append(delegations, del)
		del = stakingtypes.NewDelegation(genAccs[1].GetAddress(), val.Address.Bytes(), shares.Sub(delShares))
		delegations = append(delegations, del)
	}

	// set validators and delegations
	var (
		stakingGenesis stakingtypes.GenesisState
		bondDenom      string
	)

	if genesisState[stakingtypes.ModuleName] != nil {
		app.AppCodec().MustUnmarshalJSON(genesisState[stakingtypes.ModuleName], &stakingGenesis)
		bondDenom = stakingGenesis.Params.BondDenom
	} else {
		bondDenom = sdk.DefaultBondDenom
	}

	// add bonded amount to bonded pool module account
	balances = append(balances, banktypes.Balance{
		Address: authtypes.NewModuleAddress(stakingtypes.BondedPoolName).String(),
		Coins:   sdk.Coins{sdk.NewCoin(bondDenom, totalBonded)},
	})
	// add unbonded amount
	balances = append(balances, banktypes.Balance{
		Address: authtypes.NewModuleAddress(stakingtypes.NotBondedPoolName).String(),
		Coins:   sdk.Coins{sdk.NewCoin(bondDenom, totalUnbonded)},
	})

	stakingGenesis.Params.MaxValidators = 2
	stakingGenesis.Params.UnbondingTime = UNBONDING_P

	// set validators and delegations
	stakingGenesis = *stakingtypes.NewGenesisState(stakingGenesis.Params, validators, delegations)
	genesisState[stakingtypes.ModuleName] = app.AppCodec().MustMarshalJSON(&stakingGenesis)

	// update total supply
	bankGenesis := banktypes.NewGenesisState(banktypes.DefaultGenesisState().Params, balances, sdk.NewCoins(), []banktypes.Metadata{})
	genesisState[banktypes.ModuleName] = app.AppCodec().MustMarshalJSON(bankGenesis)

	stateBytes, err := json.MarshalIndent(genesisState, "", " ")
	require.NoError(t, err)

	// init chain will set the validator set and initialize the genesis accounts
	app.InitChain(
		abci.RequestInitChain{
			ChainId:    chainID,
			Validators: []abci.ValidatorUpdate{},
			// TODO: I'm not sure if it's OK to change this, the original is
			// ibc-go/testing/simapp/test_helpers.go::DefaultConsensusParams
			ConsensusParams: DTDefaultConsensusParams,
			AppStateBytes:   stateBytes,
		},
	)

	// commit genesis changes
	app.Commit()

	header := tmproto.Header{
		ChainID:            chainID,
		Height:             app.LastBlockHeight() + 1,
		AppHash:            app.LastCommitID().Hash,
		ValidatorsHash:     valSet.Hash(),
		NextValidatorsHash: valSet.Hash(),
	}

	app.BeginBlock(
		abci.RequestBeginBlock{
			Header: header,
		},
	)

	return app
}

func NewDTTestChainWithValSet(t *testing.T, coord *ibctesting.Coordinator, appIniter ibctesting.AppIniter, chainID string, valSet *tmtypes.ValidatorSet, signers map[string]tmtypes.PrivValidator) *ibctesting.TestChain {
	genAccs := []authtypes.GenesisAccount{}
	genBals := []banktypes.Balance{}
	senderAccs := []ibctesting.SenderAccount{}

	// generate genesis accounts
	for i := 0; i < ibctesting.MaxAccounts; i++ {
		senderPrivKey := secp256k1.GenPrivKey()
		acc := authtypes.NewBaseAccount(senderPrivKey.PubKey().Address().Bytes(), senderPrivKey.PubKey(), uint64(i), 0)
		// TODO: this weird number is a relic from having
		// extra validators who aren't created in the genesis
		// but are added later
		amount, ok := sdk.NewIntFromString("1000000000030000")
		require.True(t, ok)

		balance := banktypes.Balance{
			Address: acc.GetAddress().String(),
			Coins:   sdk.NewCoins(sdk.NewCoin(sdk.DefaultBondDenom, amount)),
		}

		genAccs = append(genAccs, acc)
		genBals = append(genBals, balance)

		senderAcc := ibctesting.SenderAccount{
			SenderAccount: acc,
			SenderPrivKey: senderPrivKey,
		}

		senderAccs = append(senderAccs, senderAcc)
	}

	app := DTSetupWithGenesisValSet(t, appIniter, valSet, genAccs, chainID, genBals...)

	header := tmproto.Header{
		ChainID: chainID,
		Height:  1,
		Time:    coord.CurrentTime.UTC(),
	}

	txConfig := app.GetTxConfig()

	// create an account to send transactions from
	chain := &ibctesting.TestChain{
		T:              t,
		Coordinator:    coord,
		ChainID:        chainID,
		App:            app,
		CurrentHeader:  header,
		QueryServer:    app.GetIBCKeeper(),
		TxConfig:       txConfig,
		Codec:          app.AppCodec(),
		Vals:           valSet,
		NextVals:       valSet,
		Signers:        signers,
		SenderPrivKey:  senderAccs[0].SenderPrivKey,
		SenderAccount:  senderAccs[0].SenderAccount,
		SenderAccounts: senderAccs,
	}

	coord.CommitBlock(chain)

	return chain
}

// NewTestChain initializes a new test chain with a default of 4 validators
// Use this function if the tests do not need custom control over the validator set
func NewDTTestChain(t *testing.T, coord *ibctesting.Coordinator, appIniter ibctesting.AppIniter, chainID string) (*ibctesting.TestChain, []sdk.ValAddress) {
	// generate validators private/public key
	var (
		validatorsPerChain = 2
		validators         []*tmtypes.Validator
		signersByAddress   = make(map[string]tmtypes.PrivValidator, validatorsPerChain)
	)

	addresses := []sdk.ValAddress{}

	for i := 0; i < validatorsPerChain; i++ {
		privVal := mock.NewPV()
		pubKey, err := privVal.GetPubKey()
		require.NoError(t, err)
		// TODO: the power here needs to be computed another way
		validators = append(validators, tmtypes.NewValidator(pubKey, int64((5-i)*TOKEN_SCALAR)))
		signersByAddress[pubKey.Address().String()] = privVal

		addr, err := sdk.ValAddressFromHex(pubKey.Address().String())
		require.NoError(t, err)
		addresses = append(addresses, addr)
	}

	// construct validator set;
	// Note that the validators are sorted by voting power
	// or, if equal, by address lexical order
	valSet := tmtypes.NewValidatorSet(validators)

	return NewDTTestChainWithValSet(t, coord, appIniter, chainID, valSet, signersByAddress), addresses
}

func NewDTProviderConsumerCoordinator(t *testing.T) (*ibctesting.Coordinator, *ibctesting.TestChain, *ibctesting.TestChain, []sdk.ValAddress) {
	coordinator := simapp.NewBasicCoordinator(t)
	chainID := ibctesting.GetChainID(0)
	var addresses []sdk.ValAddress
	coordinator.Chains[chainID], addresses = NewDTTestChain(t, coordinator, simapp.SetupTestingappProvider, chainID)
	providerChain := coordinator.GetChain(chainID)
	chainID = ibctesting.GetChainID(1)
	coordinator.Chains[chainID] = NewDTTestChainWithValSet(t, coordinator, simapp.SetupTestingAppConsumer, chainID, providerChain.Vals, providerChain.Signers)
	consumerChain := coordinator.GetChain(chainID)
	return coordinator, providerChain, consumerChain, addresses
}
