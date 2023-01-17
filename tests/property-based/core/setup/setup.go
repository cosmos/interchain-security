package setup

import (
	"encoding/json"
	"testing"
	"time"

	codectypes "github.com/cosmos/cosmos-sdk/codec/types"
	"github.com/cosmos/cosmos-sdk/crypto/keys/secp256k1"
	sdk "github.com/cosmos/cosmos-sdk/types"
	authtypes "github.com/cosmos/cosmos-sdk/x/auth/types"
	banktypes "github.com/cosmos/cosmos-sdk/x/bank/types"
	"github.com/stretchr/testify/assert"
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

const P = "provider"
const C = "consumer"

var varInitState InitState

// ValStates represents the total delegation
// and bond status of a validator
type ValStates struct {
	Delegation           []int
	Tokens               []int
	ValidatorExtraTokens []int
	Status               []stakingtypes.BondStatus
}

type InitState struct {
	NumValidators          int
	MaxValidators          int
	InitialDelegatorTokens int
	SlashDoublesign        sdk.Dec
	SlashDowntime          sdk.Dec
	UnbondingP             time.Duration
	UnbondingC             time.Duration
	Trusting               time.Duration
	MaxClockDrift          time.Duration
	BlockInterval          time.Duration
	ConsensusParams        *abci.ConsensusParams
	ValStates              ValStates
	MaxEntries             int
}

func init() {
	//	tokens === power
	sdk.DefaultPowerReduction = sdk.NewInt(1)
	/*
		These initial values heuristically lead to reasonably good exploration of behaviors.
	*/
	varInitState = InitState{
		NumValidators:          4,
		MaxValidators:          2,
		InitialDelegatorTokens: 10000000000000,
		SlashDoublesign:        sdk.NewDec(0),
		SlashDowntime:          sdk.NewDec(0),
		UnbondingP:             time.Second * 70,
		UnbondingC:             time.Second * 50,
		Trusting:               time.Second * 49, // Must be less than least unbonding
		MaxClockDrift:          time.Second * 10000,
		BlockInterval:          time.Second * 6, // Time between blocks in setup
		ValStates: ValStates{
			Delegation:           []int{4000, 3000, 2000, 1000},
			Tokens:               []int{5000, 4000, 3000, 2000},
			ValidatorExtraTokens: []int{1000, 1000, 1000, 1000},
			Status: []stakingtypes.BondStatus{stakingtypes.Bonded, stakingtypes.Bonded,
				stakingtypes.Unbonded, stakingtypes.Unbonded},
		},
		MaxEntries: 1000000,
		ConsensusParams: &abci.ConsensusParams{
			Block: &abci.BlockParams{
				MaxBytes: 9223372036854775807,
				MaxGas:   9223372036854775807,
			},
			Evidence: &tmproto.EvidenceParams{
				MaxAgeNumBlocks: 302400,
				MaxAgeDuration:  504 * time.Hour, // 3 weeks
				MaxBytes:        10000,
			},
			Validator: &tmproto.ValidatorParams{
				PubKeyTypes: []string{
					tmtypes.ABCIPubKeyTypeEd25519,
				},
			},
		},
	}
}

type builder struct {
	t            *testing.T
	path         *ibctesting.Path
	coordinator  *ibctesting.Coordinator
	valAddresses []sdk.ValAddress
	initState    InitState
}

func (b *builder) provider() *ibctesting.TestChain {
	return b.coordinator.GetChain(ibctesting.GetChainID(0))
}

func (b *builder) consumer() *ibctesting.TestChain {
	return b.coordinator.GetChain(ibctesting.GetChainID(1))
}

func (b *builder) providerCtx() sdk.Context {
	return b.provider().GetContext()
}

func (b *builder) consumerCtx() sdk.Context {
	return b.consumer().GetContext()
}

func (b *builder) providerStakingKeeper() stakingkeeper.Keeper {
	return b.provider().App.(*appProvider.App).StakingKeeper
}

func (b *builder) providerSlashingKeeper() slashingkeeper.Keeper {
	return b.provider().App.(*appProvider.App).SlashingKeeper
}

func (b *builder) providerKeeper() providerkeeper.Keeper {
	return b.provider().App.(*appProvider.App).ProviderKeeper
}

func (b *builder) consumerKeeper() consumerkeeper.Keeper {
	return b.consumer().App.(*appConsumer.App).ConsumerKeeper
}

func (b *builder) providerEndpoint() *ibctesting.Endpoint {
	return b.path.EndpointB
}

func (b *builder) consumerEndpoint() *ibctesting.Endpoint {
	return b.path.EndpointA
}

func (b *builder) validator(i int64) sdk.ValAddress {
	return b.valAddresses[i]
}

func (b *builder) consAddr(i int64) sdk.ConsAddress {
	return sdk.ConsAddress(b.validator(i))
}

// getTestValidator returns the validator private key using the given seed index
func (b *builder) getTestValidator(seedIx int) *testcrypto.CryptoIdentity {
	seed := make([]byte, 32)
	for i := 0; i < 32; i++ {
		seed[i] = byte(seedIx)
	}
	return testcrypto.NewCryptoIdentityFromBytesSeed(seed)
}

func (b *builder) getAppBytesAndSenders(
	chainID string,
	app ibctesting.TestingApp,
	genesis map[string]json.RawMessage,
	validators *tmtypes.ValidatorSet,
) ([]byte, []ibctesting.SenderAccount) {

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
		assert.Equal(b.t, status, stakingtypes.Bonded, "All genesis validators should be bonded")
		sumBonded = sumBonded.Add(tokens)
		// delegator account receives delShares shares
		delShares := sdk.NewDec(int64(delegation))
		// validator has additional sumShares due to extra units
		sumShares := sdk.NewDec(int64(delegation + extra))

		pk, err := cryptocodec.FromTmPubKeyInterface(val.PubKey)
		assert.NoError(b.t, err)
		pkAny, err := codectypes.NewAnyWithValue(pk)
		assert.NoError(b.t, err)

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
	assert.NoError(b.t, err)

	return stateBytes, senderAccounts

}

func (b *builder) newChain(
	coord *ibctesting.Coordinator,
	appInit ibctesting.AppIniter,
	chainID string,
	validators *tmtypes.ValidatorSet,
	signers map[string]tmtypes.PrivValidator,
) *ibctesting.TestChain {

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
		T:           b.t,
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

func (b *builder) createValidators() (*tmtypes.ValidatorSet, map[string]tmtypes.PrivValidator, []sdk.ValAddress) {
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

func (b *builder) createProviderAndConsumer() {

	coordinator := ibctesting.NewCoordinator(b.t, 0)

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
func (b *builder) setSigningInfos() {
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

// delegate is used to delegate tokens to newly created
// validators in the setup process.
func (b *builder) delegate(del int, val sdk.ValAddress, amt int64) {
	d := b.provider().SenderAccounts[del].SenderAccount.GetAddress()
	coins := sdk.NewCoin(sdk.DefaultBondDenom, sdk.NewInt(amt))
	msg := stakingtypes.NewMsgDelegate(d, val, coins)
	pskServer := stakingkeeper.NewMsgServerImpl(b.providerStakingKeeper())
	_, err := pskServer.Delegate(sdk.WrapSDKContext(b.providerCtx()), msg)
	assert.NoError(b.t, err)
}

// addValidatorToStakingModule creates an additional validator with zero commission
// and zero tokens (zero voting power).
func (b *builder) addValidatorToStakingModule(testVal *testcrypto.CryptoIdentity) {
	coin := sdk.NewCoin(sdk.DefaultBondDenom, sdk.NewInt(0))
	msg, err := stakingtypes.NewMsgCreateValidator(
		testVal.SDKValAddress(),
		testVal.SDKPubKey(),
		coin,
		stakingtypes.Description{},
		stakingtypes.NewCommissionRates(sdk.ZeroDec(), sdk.ZeroDec(), sdk.ZeroDec()),
		sdk.ZeroInt())
	assert.NoError(b.t, err)
	pskServer := stakingkeeper.NewMsgServerImpl(b.providerStakingKeeper())
	_, _ = pskServer.CreateValidator(sdk.WrapSDKContext(b.providerCtx()), msg)
}

func (b *builder) addExtraProviderValidators() {

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

	for i := range b.initState.ValStates.Status {
		if b.initState.ValStates.Status[i] == stakingtypes.Unbonded {
			del := b.initState.ValStates.Delegation[i]
			extra := b.initState.ValStates.ValidatorExtraTokens[i]
			b.delegate(0, b.validator(int64(i)), int64(del))
			b.delegate(1, b.validator(int64(i)), int64(extra))
		}
	}
}

func (b *builder) setProviderParams() {
	// Set the slash factors on the provider to match the model
	slash := b.providerSlashingKeeper().GetParams(b.providerCtx())
	slash.SlashFractionDoubleSign = b.initState.SlashDoublesign
	slash.SlashFractionDowntime = b.initState.SlashDowntime
	b.providerSlashingKeeper().SetParams(b.providerCtx(), slash)

	// Set the throttle factors
	throttle := b.providerKeeper().GetParams(b.providerCtx())
	throttle.SlashMeterReplenishFraction = "1.0"
	throttle.SlashMeterReplenishPeriod = time.Second * 1
	b.providerKeeper().SetParams(b.providerCtx(), throttle)
}

func (b *builder) configurePath() {
	b.path = ibctesting.NewPath(b.consumer(), b.provider())
	b.consumerEndpoint().ChannelConfig.PortID = ccv.ConsumerPortID
	b.providerEndpoint().ChannelConfig.PortID = ccv.ProviderPortID
	b.consumerEndpoint().ChannelConfig.Version = ccv.Version
	b.providerEndpoint().ChannelConfig.Version = ccv.Version
	b.consumerEndpoint().ChannelConfig.Order = channeltypes.ORDERED
	b.providerEndpoint().ChannelConfig.Order = channeltypes.ORDERED
}

func (b *builder) createProvidersLocalClient() {
	// Configure and create the consumer Client
	tmCfg := b.providerEndpoint().ClientConfig.(*ibctesting.TendermintConfig)
	tmCfg.UnbondingPeriod = b.initState.UnbondingC
	tmCfg.TrustingPeriod = b.initState.Trusting
	tmCfg.MaxClockDrift = b.initState.MaxClockDrift
	err := b.providerEndpoint().CreateClient()
	assert.NoError(b.t, err)
	// Create the Consumer chain ID mapping in the provider state
	b.providerKeeper().SetConsumerClientId(b.providerCtx(), b.consumer().ChainID, b.providerEndpoint().ClientID)
}

func (b *builder) createConsumersLocalClientGenesis() *ibctmtypes.ClientState {
	tmCfg := b.consumerEndpoint().ClientConfig.(*ibctesting.TendermintConfig)
	tmCfg.UnbondingPeriod = b.initState.UnbondingP
	tmCfg.TrustingPeriod = b.initState.Trusting
	tmCfg.MaxClockDrift = b.initState.MaxClockDrift

	return ibctmtypes.NewClientState(
		b.provider().ChainID, tmCfg.TrustLevel, tmCfg.TrustingPeriod, tmCfg.UnbondingPeriod, tmCfg.MaxClockDrift,
		b.provider().LastHeader.GetHeight().(clienttypes.Height), commitmenttypes.GetSDKSpecs(),
		[]string{"upgrade", "upgradedIBCState"}, tmCfg.AllowUpdateAfterExpiry, tmCfg.AllowUpdateAfterMisbehaviour,
	)
}

func (b *builder) createConsumerGenesis(client *ibctmtypes.ClientState) *consumertypes.GenesisState {
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
	return consumertypes.NewInitialGenesisState(client, providerConsState, valUpdates, params)
}

type ZeroState struct {
	Path             *ibctesting.Path
	Addrs            []sdk.ValAddress
	HeightLastCommit int64
	TimeLastCommit   time.Time
	TrustDuration    time.Duration
}

// The state of the data returned is equivalent to the state of two chains
// after a full handshake, but the precise order of steps used to reach the
// state does not necessarily mimic the order of steps that happen in a
// live scenario.
func GetZeroState(t *testing.T) ZeroState {
	b := builder{initState: varInitState, t: t}

	b.createProviderAndConsumer()

	b.setProviderParams()

	// This is the simplest way to initialize the slash meter
	// after a change to the param value.
	b.providerKeeper().InitializeSlashMeter(b.providerCtx())

	b.addExtraProviderValidators()

	// Commit the additional validators
	b.coordinator.CommitBlock(b.provider())

	b.configurePath()

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

	simibc.BeginBlock(b.consumer(), varInitState.BlockInterval)
	simibc.BeginBlock(b.provider(), varInitState.BlockInterval)

	// Commit a block on both chains, giving us two committed headers from
	// the same time and height. This is the starting point for all our
	// data driven testing.
	lastProviderHeader, _ := simibc.EndBlock(b.provider(), func() {})
	lastConsumerHeader, _ := simibc.EndBlock(b.consumer(), func() {})

	// Want the height and time of last COMMITTED block
	heightLastCommitted := b.provider().CurrentHeader.Height
	timeLastCommitted := b.provider().CurrentHeader.Time

	// Get ready to update clients.
	simibc.BeginBlock(b.provider(), varInitState.BlockInterval)
	simibc.BeginBlock(b.consumer(), varInitState.BlockInterval)

	// Update clients to the latest header. Now everything is ready to go!
	// Ignore errors for brevity. Everything is checked in Assuptions test.
	_ = simibc.UpdateReceiverClient(b.consumerEndpoint(), b.providerEndpoint(), lastConsumerHeader)
	_ = simibc.UpdateReceiverClient(b.providerEndpoint(), b.consumerEndpoint(), lastProviderHeader)

	z := ZeroState{}
	z.Path = b.path
	z.Addrs = b.valAddresses
	z.HeightLastCommit = heightLastCommitted
	z.TimeLastCommit = timeLastCommitted
	z.TrustDuration = varInitState.Trusting
	return z

}
