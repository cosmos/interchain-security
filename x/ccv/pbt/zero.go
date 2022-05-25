package pbt

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

// DefaultConsensusParams defines the default Tendermint consensus params used in
// SimApp testing.
var PBTDefaultConsensusParams = &abci.ConsensusParams{
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

func PBTSetupWithGenesisValSet(t *testing.T, appIniter ibctesting.AppIniter, valSet *tmtypes.ValidatorSet, genAccs []authtypes.GenesisAccount, chainID string, balances ...banktypes.Balance) ibctesting.TestingApp {
	app, genesisState := appIniter()

	// set genesis accounts
	authGenesis := authtypes.NewGenesisState(authtypes.DefaultParams(), genAccs)
	genesisState[authtypes.ModuleName] = app.AppCodec().MustMarshalJSON(authGenesis)

	validators := make([]stakingtypes.Validator, 0, len(valSet.Validators))
	delegations := make([]stakingtypes.Delegation, 0, len(valSet.Validators))

	// tokens = power
	require.Equal(t, sdk.NewInt(1), sdk.DefaultPowerReduction)
	require.Equal(t, 4, len(valSet.Validators))

	initialModelState := InitialModelState{
		// TODO: multiply by some 1000's
		Delegation: []int64{4, 3, 2, 1},
		Status:     []stakingtypes.BondStatus{stakingtypes.Bonded, stakingtypes.Bonded, stakingtypes.Unbonded, stakingtypes.Unbonded},
	}

	totalBonded := sdk.NewInt(0)
	totalUnbonded := sdk.NewInt(0)

	for i, val := range valSet.Validators {
		delegation := initialModelState.Delegation[i]
		status := initialModelState.Status[i]

		tokens := sdk.NewInt(delegation + 1)
		if status == stakingtypes.Bonded {
			totalBonded = totalBonded.Add(tokens)
		}
		if status == stakingtypes.Unbonded {
			totalUnbonded = totalUnbonded.Add(tokens)
		}
		delShares := sdk.NewDec(delegation)
		shares := sdk.NewDec(delegation + 1)

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
	var stakingGenesis stakingtypes.GenesisState
	app.AppCodec().MustUnmarshalJSON(genesisState[stakingtypes.ModuleName], &stakingGenesis)

	bondDenom := stakingGenesis.Params.BondDenom

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
			ConsensusParams: PBTDefaultConsensusParams,
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

	// TODO: not sure if this is in right place or header is correct
	params := app.GetStakingKeeper().GetParams(app.GetBaseApp().NewContext(false, header))
	params.UnbondingTime = 5 * time.Second
	params.MaxValidators = 1
	app.GetStakingKeeper().SetParams(app.GetBaseApp().NewContext(false, header), params)

	app.BeginBlock(
		abci.RequestBeginBlock{
			Header: header,
		},
	)

	return app
}

func NewPBTTestChainWithValSet(t *testing.T, coord *ibctesting.Coordinator, appIniter ibctesting.AppIniter, chainID string, valSet *tmtypes.ValidatorSet, signers map[string]tmtypes.PrivValidator) *ibctesting.TestChain {
	genAccs := []authtypes.GenesisAccount{}
	genBals := []banktypes.Balance{}
	senderAccs := []ibctesting.SenderAccount{}

	// generate genesis accounts
	for i := 0; i < ibctesting.MaxAccounts; i++ {
		senderPrivKey := secp256k1.GenPrivKey()
		acc := authtypes.NewBaseAccount(senderPrivKey.PubKey().Address().Bytes(), senderPrivKey.PubKey(), uint64(i), 0)
		amount, ok := sdk.NewIntFromString("1000000000000000000")
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

	app := PBTSetupWithGenesisValSet(t, appIniter, valSet, genAccs, chainID, genBals...)

	// create current header and call begin block
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
func NewPBTTestChain(t *testing.T, coord *ibctesting.Coordinator, appIniter ibctesting.AppIniter, chainID string) *ibctesting.TestChain {
	// generate validators private/public key
	var (
		validatorsPerChain = 4
		validators         []*tmtypes.Validator
		signersByAddress   = make(map[string]tmtypes.PrivValidator, validatorsPerChain)
	)

	for i := 0; i < validatorsPerChain; i++ {
		privVal := mock.NewPV()
		pubKey, err := privVal.GetPubKey()
		require.NoError(t, err)
		validators = append(validators, tmtypes.NewValidator(pubKey, 1))
		signersByAddress[pubKey.Address().String()] = privVal
	}

	// construct validator set;
	// Note that the validators are sorted by voting power
	// or, if equal, by address lexical order
	valSet := tmtypes.NewValidatorSet(validators)

	return NewPBTTestChainWithValSet(t, coord, appIniter, chainID, valSet, signersByAddress)
}

func NewPBTProviderConsumerCoordinator(t *testing.T) (*ibctesting.Coordinator, *ibctesting.TestChain, *ibctesting.TestChain) {
	coordinator := simapp.NewBasicCoordinator(t)
	chainID := ibctesting.GetChainID(0)
	coordinator.Chains[chainID] = NewPBTTestChain(t, coordinator, simapp.SetupTestingAppProvider, chainID)
	providerChain := coordinator.GetChain(chainID)
	chainID = ibctesting.GetChainID(1)
	coordinator.Chains[chainID] = NewPBTTestChainWithValSet(t, coordinator, simapp.SetupTestingAppConsumer, chainID, providerChain.Vals, providerChain.Signers)
	consumerChain := coordinator.GetChain(chainID)
	return coordinator, providerChain, consumerChain
}
