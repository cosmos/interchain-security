package core

import (
	"bytes"
	"encoding/json"
	"time"

	codectypes "github.com/cosmos/cosmos-sdk/codec/types"
	"github.com/cosmos/cosmos-sdk/crypto/keys/secp256k1"
	sdk "github.com/cosmos/cosmos-sdk/types"
	authtypes "github.com/cosmos/cosmos-sdk/x/auth/types"
	banktypes "github.com/cosmos/cosmos-sdk/x/bank/types"
	"github.com/stretchr/testify/require"
	"github.com/stretchr/testify/suite"
	abci "github.com/tendermint/tendermint/abci/types"
	tmproto "github.com/tendermint/tendermint/proto/tendermint/types"
	tmtypes "github.com/tendermint/tendermint/types"

	ibctesting "github.com/cosmos/interchain-security/legacy_ibc_testing/testing"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	commitmenttypes "github.com/cosmos/ibc-go/v3/modules/core/23-commitment/types"
	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"

	slashingkeeper "github.com/cosmos/cosmos-sdk/x/slashing/keeper"
	slashingtypes "github.com/cosmos/cosmos-sdk/x/slashing/types"
	stakingkeeper "github.com/cosmos/cosmos-sdk/x/staking/keeper"
	appConsumer "github.com/cosmos/interchain-security/app/consumer"
	appProvider "github.com/cosmos/interchain-security/app/provider"
	icstestingutils "github.com/cosmos/interchain-security/testutil/ibc_testing"
	simibc "github.com/cosmos/interchain-security/testutil/simibc"
	consumerkeeper "github.com/cosmos/interchain-security/x/ccv/consumer/keeper"
	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
	providerkeeper "github.com/cosmos/interchain-security/x/ccv/provider/keeper"

	ccv "github.com/cosmos/interchain-security/x/ccv/types"

	testcrypto "github.com/cosmos/interchain-security/testutil/crypto"
)

type Builder struct {
	suite          *suite.Suite
	link           simibc.OrderedLink
	path           *ibctesting.Path
	coordinator    *ibctesting.Coordinator
	clientHeaders  map[string][]*ibctmtypes.Header
	mustBeginBlock map[string]bool
	valAddresses   []sdk.ValAddress
	initState      InitState
}

func (b *Builder) chainID(chain string) string {
	return map[string]string{P: ibctesting.GetChainID(0), C: ibctesting.GetChainID(1)}[chain]
}

func (b *Builder) otherID(chainID string) string {
	return map[string]string{ibctesting.GetChainID(0): ibctesting.GetChainID(1), ibctesting.GetChainID(1): ibctesting.GetChainID(0)}[chainID]
}

func (b *Builder) provider() *ibctesting.TestChain {
	return b.coordinator.GetChain(ibctesting.GetChainID(0))
}

func (b *Builder) consumer() *ibctesting.TestChain {
	return b.coordinator.GetChain(ibctesting.GetChainID(1))
}

func (b *Builder) providerCtx() sdk.Context {
	return b.provider().GetContext()
}

func (b *Builder) consumerCtx() sdk.Context {
	return b.consumer().GetContext()
}

func (b *Builder) providerStakingKeeper() stakingkeeper.Keeper {
	return b.provider().App.(*appProvider.App).StakingKeeper
}

func (b *Builder) providerSlashingKeeper() slashingkeeper.Keeper {
	return b.provider().App.(*appProvider.App).SlashingKeeper
}

func (b *Builder) providerKeeper() providerkeeper.Keeper {
	return b.provider().App.(*appProvider.App).ProviderKeeper
}

func (b *Builder) consumerKeeper() consumerkeeper.Keeper {
	return b.consumer().App.(*appConsumer.App).ConsumerKeeper
}

func (b *Builder) endpointFromID(chainID string) *ibctesting.Endpoint {
	return map[string]*ibctesting.Endpoint{ibctesting.GetChainID(0): b.path.EndpointB, ibctesting.GetChainID(1): b.path.EndpointA}[chainID]
}

func (b *Builder) endpoint(chain string) *ibctesting.Endpoint {
	return map[string]*ibctesting.Endpoint{P: b.path.EndpointB, C: b.path.EndpointA}[chain]
}

func (b *Builder) validator(i int64) sdk.ValAddress {
	return b.valAddresses[i]
}

func (b *Builder) consAddr(i int64) sdk.ConsAddress {
	return sdk.ConsAddress(b.validator(i))
}

// getTestValidator returns the validator private key using the given seed index
func (b *Builder) getTestValidator(seedIx int) *testcrypto.CryptoIdentity {
	return testcrypto.NewCryptoIdentityFromBytesSeed([]byte(b.initState.PKSeeds[seedIx]))
}

func (b *Builder) getAppBytesAndSenders(chainID string, app ibctesting.TestingApp, genesis map[string]json.RawMessage,
	validators *tmtypes.ValidatorSet) ([]byte, []ibctesting.SenderAccount) {

	accounts := []authtypes.GenesisAccount{}
	balances := []banktypes.Balance{}
	senderAccounts := []ibctesting.SenderAccount{}

	// Create genesis accounts.
	for i := 0; i < b.initState.MaxValidators; i++ {
		pk := secp256k1.GenPrivKey()
		acc := authtypes.NewBaseAccount(pk.PubKey().Address().Bytes(), pk.PubKey(), uint64(i), 0)

		// Give enough funds for many delegations
		// Extra units are to delegate to extra validators created later
		// in order to bond them and still have INITIAL_DELEGATOR_TOKENS remaining
		extra := 0
		for j := 0; j < b.initState.NumValidators; j++ {
			if b.initState.ValStates.Status[j] != stakingtypes.Bonded {
				extra += b.initState.ValStates.Delegation[j]
			}
		}
		amt := uint64(b.initState.InitialDelegatorTokens + extra)

		bal := banktypes.Balance{
			Address: acc.GetAddress().String(),
			Coins:   sdk.NewCoins(sdk.NewCoin(sdk.DefaultBondDenom, sdk.NewIntFromUint64(amt))),
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

	stakingValidators := make([]stakingtypes.Validator, 0, len(validators.Validators))
	delegations := make([]stakingtypes.Delegation, 0, len(validators.Validators))

	// Sum bonded is needed for BondedPool account
	sumBonded := sdk.NewInt(0)

	for i, val := range validators.Validators {
		status := b.initState.ValStates.Status[i]
		delegation := b.initState.ValStates.Delegation[i]
		extra := b.initState.ValStates.ValidatorExtraTokens[i]

		tokens := sdk.NewInt(int64(delegation + extra))
		b.suite.Require().Equal(status, stakingtypes.Bonded, "All genesis validators should be bonded")
		sumBonded = sumBonded.Add(tokens)
		// delegator account receives delShares shares
		delShares := sdk.NewDec(int64(delegation))
		// validator has additional sumShares due to extra units
		sumShares := sdk.NewDec(int64(delegation + extra))

		pk, err := cryptocodec.FromTmPubKeyInterface(val.PubKey)
		require.NoError(b.suite.T(), err)
		pkAny, err := codectypes.NewAnyWithValue(pk)
		require.NoError(b.suite.T(), err)

		validator := stakingtypes.Validator{
			OperatorAddress:   sdk.ValAddress(val.Address).String(),
			ConsensusPubkey:   pkAny,
			Jailed:            false,
			Status:            status,
			Tokens:            tokens,
			DelegatorShares:   sumShares,
			Description:       stakingtypes.Description{},
			UnbondingHeight:   int64(0),
			UnbondingTime:     time.Unix(0, 0).UTC(),
			Commission:        stakingtypes.NewCommission(sdk.ZeroDec(), sdk.ZeroDec(), sdk.ZeroDec()),
			MinSelfDelegation: sdk.ZeroInt(),
		}

		stakingValidators = append(stakingValidators, validator)

		// Store delegation from the model delegator account
		delegations = append(delegations, stakingtypes.NewDelegation(accounts[0].GetAddress(), val.Address.Bytes(), delShares))
		// Remaining delegation is from extra account
		delegations = append(delegations, stakingtypes.NewDelegation(accounts[1].GetAddress(), val.Address.Bytes(), sumShares.Sub(delShares)))
	}

	bondDenom := sdk.DefaultBondDenom
	genesisStaking := stakingtypes.GenesisState{}

	if genesis[stakingtypes.ModuleName] != nil {
		// If staking module genesis already exists
		app.AppCodec().MustUnmarshalJSON(genesis[stakingtypes.ModuleName], &genesisStaking)
		bondDenom = genesisStaking.Params.BondDenom
	}

	// Set model parameters
	genesisStaking.Params.MaxEntries = uint32(b.initState.MaxEntries)
	genesisStaking.Params.MaxValidators = uint32(b.initState.MaxValidators)
	genesisStaking.Params.UnbondingTime = b.initState.UnbondingP
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
	genesisBank := banktypes.NewGenesisState(banktypes.DefaultGenesisState().Params, balances, sdk.NewCoins(), []banktypes.Metadata{})
	genesis[banktypes.ModuleName] = app.AppCodec().MustMarshalJSON(genesisBank)

	stateBytes, err := json.MarshalIndent(genesis, "", " ")
	require.NoError(b.suite.T(), err)

	return stateBytes, senderAccounts

}

func (b *Builder) newChain(coord *ibctesting.Coordinator, appInit ibctesting.AppIniter, chainID string,
	validators *tmtypes.ValidatorSet, signers map[string]tmtypes.PrivValidator) *ibctesting.TestChain {

	app, genesis := appInit()

	stateBytes, senderAccounts := b.getAppBytesAndSenders(chainID, app, genesis, validators)

	app.InitChain(
		abci.RequestInitChain{
			ChainId:         chainID,
			Validators:      []abci.ValidatorUpdate{},
			ConsensusParams: b.initState.ConsensusParams,
			AppStateBytes:   stateBytes,
		},
	)

	app.Commit()

	app.BeginBlock(
		abci.RequestBeginBlock{
			Header: tmproto.Header{
				ChainID:            chainID,
				Height:             app.LastBlockHeight() + 1,
				AppHash:            app.LastCommitID().Hash,
				ValidatorsHash:     validators.Hash(),
				NextValidatorsHash: validators.Hash(),
			},
		},
	)

	chain := &ibctesting.TestChain{
		T:           b.suite.T(),
		Coordinator: coord,
		ChainID:     chainID,
		App:         app,
		CurrentHeader: tmproto.Header{
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

func (b *Builder) createValidators() (*tmtypes.ValidatorSet, map[string]tmtypes.PrivValidator, []sdk.ValAddress) {
	addresses := []sdk.ValAddress{}
	signers := map[string]tmtypes.PrivValidator{}
	validators := []*tmtypes.Validator{}

	for i, power := range b.initState.ValStates.Tokens {
		if b.initState.ValStates.Status[i] != stakingtypes.Bonded {
			continue
		}
		testVal := b.getTestValidator(i)
		signers[testVal.TMCryptoPubKey().Address().String()] = testVal
		addresses = append(addresses, testVal.SDKValAddress())
		validators = append(validators, testVal.TMValidator(int64(power)))
	}

	return tmtypes.NewValidatorSet(validators), signers, addresses
}

func (b *Builder) createChains() {

	coordinator := ibctesting.NewCoordinator(b.suite.T(), 0)

	// Create validators
	validators, signers, addresses := b.createValidators()
	// Create provider
	coordinator.Chains[ibctesting.GetChainID(0)] = b.newChain(coordinator, icstestingutils.ProviderAppIniter, ibctesting.GetChainID(0), validators, signers)
	// Create consumer, using the same validators.
	coordinator.Chains[ibctesting.GetChainID(1)] = b.newChain(coordinator, icstestingutils.ConsumerAppIniter, ibctesting.GetChainID(1), validators, signers)

	b.coordinator = coordinator
	b.valAddresses = addresses

}

// setSigningInfos sets the validator signing info in the provider Slashing module
func (b *Builder) setSigningInfos() {
	for i := 0; i < b.initState.NumValidators; i++ {
		info := slashingtypes.NewValidatorSigningInfo(
			b.consAddr(int64(i)),
			b.provider().CurrentHeader.GetHeight(),
			0,
			time.Unix(0, 0),
			false,
			0,
		)
		b.providerSlashingKeeper().SetValidatorSigningInfo(b.providerCtx(), b.consAddr(int64(i)), info)
	}
}

// Checks that the lexicographic ordering of validator addresses as computed in
// the staking module match the ordering of validators in the model.
func (b *Builder) ensureValidatorLexicographicOrderingMatchesModel() {

	check := func(lesser sdk.ValAddress, greater sdk.ValAddress) {
		lesserV, _ := b.providerStakingKeeper().GetValidator(b.providerCtx(), lesser)
		greaterV, _ := b.providerStakingKeeper().GetValidator(b.providerCtx(), greater)
		lesserKey := stakingtypes.GetValidatorsByPowerIndexKey(lesserV, sdk.DefaultPowerReduction)
		greaterKey := stakingtypes.GetValidatorsByPowerIndexKey(greaterV, sdk.DefaultPowerReduction)
		// The result will be 0 if a==b, -1 if a < b, and +1 if a > b.
		res := bytes.Compare(lesserKey, greaterKey)
		// Confirm that validator precedence is the same in code as in model
		b.suite.Require().Equal(-1, res)
	}

	// In order to match the model to the system under test it is necessary
	// to enforce a strict lexicographic ordering on the validators.
	// We must do this because the staking module will break ties when
	// deciding the active validator set by comparing addresses lexicographically.
	// Thus, we assert here that the ordering in the model matches the ordering
	// in the SUT.
	for i := range b.valAddresses[:len(b.valAddresses)-1] {
		// validators are chosen sorted descending in the staking module
		greater := b.valAddresses[i]
		lesser := b.valAddresses[i+1]
		check(lesser, greater)
	}
}

// delegate is used to delegate tokens to newly created
// validators in the setup process.
func (b *Builder) delegate(del int, val sdk.ValAddress, amt int64) {
	d := b.provider().SenderAccounts[del].SenderAccount.GetAddress()
	coins := sdk.NewCoin(sdk.DefaultBondDenom, sdk.NewInt(amt))
	msg := stakingtypes.NewMsgDelegate(d, val, coins)
	pskServer := stakingkeeper.NewMsgServerImpl(b.providerStakingKeeper())
	_, err := pskServer.Delegate(sdk.WrapSDKContext(b.providerCtx()), msg)
	b.suite.Require().NoError(err)
}

// addValidatorToStakingModule creates an additional validator with zero commission
// and zero tokens (zero voting power).
func (b *Builder) addValidatorToStakingModule(testVal *testcrypto.CryptoIdentity) {
	coin := sdk.NewCoin(sdk.DefaultBondDenom, sdk.NewInt(0))
	msg, err := stakingtypes.NewMsgCreateValidator(
		testVal.SDKValAddress(),
		testVal.SDKPubKey(),
		coin,
		stakingtypes.Description{},
		stakingtypes.NewCommissionRates(sdk.ZeroDec(), sdk.ZeroDec(), sdk.ZeroDec()),
		sdk.ZeroInt())
	b.suite.Require().NoError(err)
	pskServer := stakingkeeper.NewMsgServerImpl(b.providerStakingKeeper())
	_, _ = pskServer.CreateValidator(sdk.WrapSDKContext(b.providerCtx()), msg)
}

func (b *Builder) addExtraProviderValidators() {

	for i, status := range b.initState.ValStates.Status {
		if status == stakingtypes.Unbonded {
			testVal := b.getTestValidator(i)
			b.addValidatorToStakingModule(testVal)
			b.valAddresses = append(b.valAddresses, testVal.SDKValAddress())
			b.provider().Signers[testVal.TMCryptoPubKey().Address().String()] = testVal
			b.consumer().Signers[testVal.TMCryptoPubKey().Address().String()] = testVal
		}
	}

	b.setSigningInfos()

	b.ensureValidatorLexicographicOrderingMatchesModel()

	for i := range b.initState.ValStates.Status {
		if b.initState.ValStates.Status[i] == stakingtypes.Unbonded {
			del := b.initState.ValStates.Delegation[i]
			extra := b.initState.ValStates.ValidatorExtraTokens[i]
			b.delegate(0, b.validator(int64(i)), int64(del))
			b.delegate(1, b.validator(int64(i)), int64(extra))
		}
	}
}

func (b *Builder) setSlashParams() {
	// Set the slash factors on the provider to match the model
	sparams := b.providerSlashingKeeper().GetParams(b.providerCtx())
	sparams.SlashFractionDoubleSign = b.initState.SlashDoublesign
	sparams.SlashFractionDowntime = b.initState.SlashDowntime
	b.providerSlashingKeeper().SetParams(b.providerCtx(), sparams)
}

func (b *Builder) configureIBCTestingPath() {
	b.path = ibctesting.NewPath(b.consumer(), b.provider())
	b.path.EndpointA.ChannelConfig.PortID = ccv.ConsumerPortID
	b.path.EndpointB.ChannelConfig.PortID = ccv.ProviderPortID
	b.path.EndpointA.ChannelConfig.Version = ccv.Version
	b.path.EndpointB.ChannelConfig.Version = ccv.Version
	b.path.EndpointA.ChannelConfig.Order = channeltypes.ORDERED
	b.path.EndpointB.ChannelConfig.Order = channeltypes.ORDERED
}

func (b *Builder) configureConsumerClientOnProvider() {
	// Configure and create the consumer Client
	tmCfg := b.path.EndpointB.ClientConfig.(*ibctesting.TendermintConfig)
	tmCfg.UnbondingPeriod = b.initState.UnbondingC
	tmCfg.TrustingPeriod = b.initState.Trusting
	tmCfg.MaxClockDrift = b.initState.MaxClockDrift
	err := b.path.EndpointB.CreateClient()
	b.suite.Require().NoError(err)
	// Create the Consumer chain ID mapping in the provider state
	b.providerKeeper().SetConsumerClientId(b.providerCtx(), b.consumer().ChainID, b.path.EndpointB.ClientID)
}

func (b *Builder) createConsumerClientGenesisState() *ibctmtypes.ClientState {
	tmCfg := ibctesting.NewTendermintConfig()
	tmCfg.UnbondingPeriod = b.initState.UnbondingP
	tmCfg.TrustingPeriod = b.initState.Trusting
	tmCfg.MaxClockDrift = b.initState.MaxClockDrift

	return ibctmtypes.NewClientState(
		b.provider().ChainID, tmCfg.TrustLevel, tmCfg.TrustingPeriod, tmCfg.UnbondingPeriod, tmCfg.MaxClockDrift,
		b.provider().LastHeader.GetHeight().(clienttypes.Height), commitmenttypes.GetSDKSpecs(),
		[]string{"upgrade", "upgradedIBCState"}, tmCfg.AllowUpdateAfterExpiry, tmCfg.AllowUpdateAfterMisbehaviour,
	)
}

func (b *Builder) createConsumerGenesis(provClient *ibctmtypes.ClientState) *consumertypes.GenesisState {
	providerConsState := b.provider().LastHeader.ConsensusState()

	valUpdates := tmtypes.TM2PB.ValidatorUpdates(b.provider().Vals)
	params := consumertypes.NewParams(
		true,
		1000, // ignore distribution
		"",   // ignore distribution
		"",   // ignore distribution
		ccv.DefaultCCVTimeoutPeriod,
		consumertypes.DefaultTransferTimeoutPeriod,
		consumertypes.DefaultConsumerRedistributeFrac,
		consumertypes.DefaultHistoricalEntries,
		b.initState.UnbondingC,
	)
	return consumertypes.NewInitialGenesisState(provClient, providerConsState, valUpdates, params)
}

func (b *Builder) configureProviderClientOnConsumer() {
	providerClientID, ok := b.consumerKeeper().GetProviderClientID(b.consumerCtx())
	if !ok {
		panic("must already have provider client on consumer chain")
	}
	b.path.EndpointA.ClientID = providerClientID
}

// The state of the data returned is equivalent to the state of two chains
// after a full handshake, but the precise order of steps used to reach the
// state does not necessarily mimic the order of steps that happen in a
// live scenario.
func GetZeroState(suite *suite.Suite, initState InitState) (path *ibctesting.Path, addrs []sdk.ValAddress, heightLastCommitted int64, timeLastCommitted int64) {
	b := Builder{initState: initState, suite: suite}

	b.createChains()

	// Create a simulated network link link
	b.createLink()

	// TODO: tidy up before merging into main
	prams := b.providerKeeper().GetParams(b.providerCtx())
	prams.SlashMeterReplenishFraction = "1.0"
	prams.SlashMeterReplenishPeriod = time.Second * 1
	b.providerKeeper().SetParams(b.providerCtx(), prams)
	b.providerKeeper().InitializeSlashMeter(b.providerCtx())
	b.setSlashParams()

	b.addExtraProviderValidators()

	// Commit the additional validators
	b.coordinator.CommitBlock(b.provider())

	b.configureIBCTestingPath()
	b.configureConsumerClientOnProvider()

	provClient := b.createConsumerClientGenesisState()
	consumerGenesis := b.createConsumerGenesis(provClient)

	b.consumerKeeper().InitGenesis(b.consumerCtx(), consumerGenesis)
	b.configureProviderClientOnConsumer()

	// Handshake
	b.coordinator.CreateConnections(b.path)
	b.coordinator.CreateChannels(b.path)

	// Send an empty VSC packet from the provider to the consumer to finish
	// the handshake. This is necessary because the model starts from a
	// completely initialized state, with a completed handshake.

	b.consumerKeeper().SetProviderChannel(b.consumerCtx(), b.endpoint(C).ChannelID)

	b.runSomeProtocolSteps()

	// Height of the last committed block (current header is not committed)
	heightLastCommitted = b.provider().CurrentHeader.Height - 1
	// Time of the last committed block (current header is not committed)
	timeLastCommitted = b.provider().CurrentHeader.Time.Add(-b.initState.BlockInterval).Unix()
	return b.path, b.valAddresses, heightLastCommitted, timeLastCommitted
}
