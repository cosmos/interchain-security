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

	ibctesting "github.com/cosmos/ibc-go/v3/testing"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	testcrypto "github.com/cosmos/interchain-security/testutil/crypto"

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

	channelkeeper "github.com/cosmos/ibc-go/v3/modules/core/04-channel/keeper"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
)

type Builder struct {
	suite           *suite.Suite
	link            simibc.OrderedLink
	path            *ibctesting.Path
	coordinator     *ibctesting.Coordinator
	clientHeaders   map[string][]*ibctmtypes.Header
	mustBeginBlock  map[string]bool
	sdkValAddresses []sdk.ValAddress
	initState       InitState
}

func (b *Builder) consumerKeeper() consumerkeeper.Keeper {
	return b.consumerApp().ConsumerKeeper
}

func (b *Builder) sdkValAddress(i int64) sdk.ValAddress {
	return b.sdkValAddresses[i]
}

func (b *Builder) ctx(chain string) sdk.Context {
	return b.chain(chain).GetContext()
}

func (b *Builder) chainID(chain string) string {
	if chain == P {
		return ibctesting.GetChainID(0)
	}
	return ibctesting.GetChainID(1)
}

func (b *Builder) otherID(chainID string) string {
	if chainID == b.chainID(P) {
		return b.chainID(C)
	}
	return b.chainID(P)
}

func (b *Builder) chain(chain string) *ibctesting.TestChain {
	return b.coordinator.GetChain(b.chainID(chain))
}

func (b *Builder) endpointFromID(chainID string) *ibctesting.Endpoint {
	if chainID == b.chainID(P) {
		return b.path.EndpointB
	}
	return b.path.EndpointA
}

func (b *Builder) endpoint(chain string) *ibctesting.Endpoint {
	return b.endpointFromID(b.chainID(chain))
}

func (b *Builder) providerApp() *appProvider.App {
	return b.chain(P).App.(*appProvider.App)
}

func (b *Builder) consumerApp() *appConsumer.App {
	return b.chain(C).App.(*appConsumer.App)
}

func (b *Builder) providerSlashingKeeper() slashingkeeper.Keeper {
	return b.providerApp().SlashingKeeper
}

func (b *Builder) providerStakingKeeper() stakingkeeper.Keeper {
	return b.providerApp().StakingKeeper
}

func (b *Builder) providerKeeper() providerkeeper.Keeper {
	return b.providerApp().ProviderKeeper
}

func (b *Builder) sdkConsAddr(i int64) sdk.ConsAddress {
	return sdk.ConsAddress(b.sdkValAddress(i))
}

// getTestValidator returns the validator private key using the given seed index
func (b *Builder) getTestValidator(seedIx int) testcrypto.CryptoIdentity {
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
			ConsensusParams: initState.ConsensusParams,
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
		signers[testVal.SDKValAddressString()] = testVal
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
	b.sdkValAddresses = addresses

}

// addValidatorToStakingModule creates an additional validator with zero commission
// and zero tokens (zero voting power).
func (b *Builder) addValidatorToStakingModule(testVal testcrypto.CryptoIdentity) {
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
	_, _ = pskServer.CreateValidator(sdk.WrapSDKContext(b.ctx(P)), msg)
}

// setSigningInfos sets the validator signing info in the provider Slashing module
func (b *Builder) setSigningInfos() {
	for i := 0; i < b.initState.NumValidators; i++ {
		info := slashingtypes.NewValidatorSigningInfo(
			b.sdkConsAddr(int64(i)),
			b.chain(P).CurrentHeader.GetHeight(),
			0,
			time.Unix(0, 0),
			false,
			0,
		)
		b.providerSlashingKeeper().SetValidatorSigningInfo(b.ctx(P), b.sdkConsAddr(int64(i)), info)
	}
}

// Checks that the lexicographic ordering of validator addresses as computed in
// the staking module match the ordering of validators in the model.
func (b *Builder) ensureValidatorLexicographicOrderingMatchesModel() {

	check := func(lesser sdk.ValAddress, greater sdk.ValAddress) {
		lesserV, _ := b.providerStakingKeeper().GetValidator(b.ctx(P), lesser)
		greaterV, _ := b.providerStakingKeeper().GetValidator(b.ctx(P), greater)
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
	for i := range b.sdkValAddresses[:len(b.sdkValAddresses)-1] {
		// validators are chosen sorted descending in the staking module
		greater := b.sdkValAddresses[i]
		lesser := b.sdkValAddresses[i+1]
		check(lesser, greater)
	}
}

// delegate is used to delegate tokens to newly created
// validators in the setup process.
func (b *Builder) delegate(del int, val sdk.ValAddress, amt int64) {
	d := b.chain(P).SenderAccounts[del].SenderAccount.GetAddress()
	coins := sdk.NewCoin(sdk.DefaultBondDenom, sdk.NewInt(amt))
	msg := stakingtypes.NewMsgDelegate(d, val, coins)
	pskServer := stakingkeeper.NewMsgServerImpl(b.providerStakingKeeper())
	_, err := pskServer.Delegate(sdk.WrapSDKContext(b.ctx(P)), msg)
	b.suite.Require().NoError(err)
}

func (b *Builder) addExtraProviderValidators() {

	for i, status := range b.initState.ValStates.Status {
		if status == stakingtypes.Unbonded {
			testVal := b.getTestValidator(i)
			b.addValidatorToStakingModule(testVal)
			b.sdkValAddresses = append(b.sdkValAddresses, testVal.SDKValAddress())
			b.chain(P).Signers[testVal.SDKValAddressString()] = testVal
			b.chain(C).Signers[testVal.SDKValAddressString()] = testVal
		}
	}

	b.setSigningInfos()

	b.ensureValidatorLexicographicOrderingMatchesModel()

	for i := range b.initState.ValStates.Status {
		if b.initState.ValStates.Status[i] == stakingtypes.Unbonded {
			del := b.initState.ValStates.Delegation[i]
			extra := b.initState.ValStates.ValidatorExtraTokens[i]
			b.delegate(0, b.sdkValAddress(int64(i)), int64(del))
			b.delegate(1, b.sdkValAddress(int64(i)), int64(extra))
		}
	}
}

func (b *Builder) setProviderSlashParams() {
	// Set the slash factors on the provider to match the model
	sparams := b.providerSlashingKeeper().GetParams(b.ctx(P))
	sparams.SlashFractionDoubleSign = b.initState.SlashDoublesign
	sparams.SlashFractionDowntime = b.initState.SlashDowntime
	b.providerSlashingKeeper().SetParams(b.ctx(P), sparams)
}

func (b *Builder) getClientConsState() (*ibctmtypes.ClientState, *ibctmtypes.ConsensusState) {
	// Set light client params to match model
	tmConfig := ibctesting.NewTendermintConfig()
	tmConfig.UnbondingPeriod = b.initState.UnbondingP
	tmConfig.TrustingPeriod = b.initState.Trusting
	tmConfig.MaxClockDrift = b.initState.MaxClockDrift

	// Create Provider client
	providerClient := ibctmtypes.NewClientState(
		b.chain(P).ChainID, tmConfig.TrustLevel, tmConfig.TrustingPeriod, tmConfig.UnbondingPeriod, tmConfig.MaxClockDrift,
		b.chain(P).LastHeader.GetHeight().(clienttypes.Height), commitmenttypes.GetSDKSpecs(),
		[]string{"upgrade", "upgradedIBCState"}, tmConfig.AllowUpdateAfterExpiry, tmConfig.AllowUpdateAfterMisbehaviour,
	)
	providerConsState := b.chain(P).LastHeader.ConsensusState()
	return providerClient, providerConsState
}

func (b *Builder) createConsumerGenesis(client *ibctmtypes.ClientState, cons *ibctmtypes.ConsensusState) *consumertypes.GenesisState {

	// Create Consumer genesis
	valUpdates := tmtypes.TM2PB.ValidatorUpdates(b.chain(P).Vals)
	params := consumertypes.NewParams(
		true,
		1000, // ignore distribution
		"",   // ignore distribution
		"",   // ignore distribution
		ccv.DefaultCCVTimeoutPeriod,
		consumertypes.DefaultTransferTimeoutPeriod,
		consumertypes.DefaultConsumerRedistributeFrac,
		consumertypes.DefaultHistoricalEntries,
		consumertypes.DefaultConsumerUnbondingPeriod,
	)
	return consumertypes.NewInitialGenesisState(client, cons, valUpdates, params)
}

func (b *Builder) createLink() {
	b.link = simibc.MakeOrderedLink()
	// init utility data structures
	b.mustBeginBlock = map[string]bool{P: true, C: true}
	b.clientHeaders = map[string][]*ibctmtypes.Header{}
	for chainID := range b.coordinator.Chains {
		b.clientHeaders[chainID] = []*ibctmtypes.Header{}
	}
}

func (b *Builder) createPath() {
	// Configure the ibc path
	b.path = ibctesting.NewPath(b.chain(C), b.chain(P))
	b.path.EndpointA.ChannelConfig.PortID = ccv.ConsumerPortID
	b.path.EndpointB.ChannelConfig.PortID = ccv.ProviderPortID
	b.path.EndpointA.ChannelConfig.Version = ccv.Version
	b.path.EndpointB.ChannelConfig.Version = ccv.Version
	b.path.EndpointA.ChannelConfig.Order = channeltypes.ORDERED
	b.path.EndpointB.ChannelConfig.Order = channeltypes.ORDERED
}

func (b *Builder) setProviderEndpointId() {
	providerClientID, ok := b.consumerKeeper().GetProviderClientID(b.ctx(C))
	if !ok {
		panic("must already have provider client on consumer chain")
	}
	b.path.EndpointA.ClientID = providerClientID
}

func (b *Builder) createProviderClient() {
	// Configure and create the consumer Client
	tmConfig := b.path.EndpointB.ClientConfig.(*ibctesting.TendermintConfig)
	tmConfig.UnbondingPeriod = b.initState.UnbondingC
	tmConfig.TrustingPeriod = b.initState.Trusting
	tmConfig.MaxClockDrift = b.initState.MaxClockDrift
	err := b.path.EndpointB.CreateClient()
	b.suite.Require().NoError(err)
}

// Manually construct and send an empty VSC packet from the provider
// to the consumer. This is necessary to complete the handshake, and thus
// match the model init state, without any additional validator power changes.
func (b *Builder) sendEmptyVSCPacketToFinishHandshake() {
	vscID := b.providerKeeper().GetValidatorSetUpdateId(b.chain(P).GetContext())

	timeout := uint64(b.chain(P).CurrentHeader.Time.Add(ccv.DefaultCCVTimeoutPeriod).UnixNano())

	pd := ccv.NewValidatorSetChangePacketData(
		[]abci.ValidatorUpdate{},
		vscID,
		nil,
	)

	seq, ok := b.chain(P).App.(*appProvider.App).GetIBCKeeper().ChannelKeeper.GetNextSequenceSend(
		b.ctx(P), ccv.ProviderPortID, b.path.EndpointB.ChannelID)

	b.suite.Require().True(ok)

	packet := channeltypes.NewPacket(pd.GetBytes(), seq, ccv.ProviderPortID, b.endpoint(P).ChannelID,
		ccv.ConsumerPortID, b.endpoint(C).ChannelID, clienttypes.Height{}, timeout)

	channelCap := b.endpoint(P).Chain.GetChannelCapability(packet.GetSourcePort(), packet.GetSourceChannel())

	err := b.endpoint(P).Chain.App.GetIBCKeeper().ChannelKeeper.SendPacket(b.ctx(P), channelCap, packet)

	b.suite.Require().NoError(err)

	// Double commit the packet
	b.endBlock(b.chainID(P))
	b.coordinator.CurrentTime = b.coordinator.CurrentTime.Add(time.Second * time.Duration(1)).UTC()
	b.beginBlock(b.chainID(P))
	b.endBlock(b.chainID(P))
	b.coordinator.CurrentTime = b.coordinator.CurrentTime.Add(time.Second * time.Duration(1)).UTC()
	b.mustBeginBlock[P] = true

	b.updateClient(b.chainID(C))

	ack, err := simibc.TryRecvPacket(b.endpoint(P), b.endpoint(C), packet)

	b.link.AddAck(b.chainID(C), ack, packet)

	b.suite.Require().NoError(err)
}

// idempotentBeginBlock begins a new block on chain
// if it is necessary to do so.
func (b *Builder) idempotentBeginBlock(chain string) {
	if b.mustBeginBlock[chain] {
		b.mustBeginBlock[chain] = false
		b.beginBlock(b.chainID(chain))
		b.updateClient(b.chainID(chain))
	}
}

func (b *Builder) beginBlock(chainID string) {
	c := b.coordinator.GetChain(chainID)
	c.CurrentHeader = tmproto.Header{
		ChainID:            c.ChainID,
		Height:             c.App.LastBlockHeight() + 1,
		AppHash:            c.App.LastCommitID().Hash,
		Time:               b.coordinator.CurrentTime,
		ValidatorsHash:     c.Vals.Hash(),
		NextValidatorsHash: c.NextVals.Hash(),
	}
	_ = c.App.BeginBlock(abci.RequestBeginBlock{Header: c.CurrentHeader})
}

func (b *Builder) updateClient(chainID string) {
	for _, header := range b.clientHeaders[b.otherID(chainID)] {
		err := simibc.UpdateReceiverClient(b.endpointFromID(b.otherID(chainID)), b.endpointFromID(chainID), header)
		if err != nil {
			b.coordinator.Fatal("updateClient")
		}
	}
	b.clientHeaders[b.otherID(chainID)] = []*ibctmtypes.Header{}
}

func (b *Builder) deliver(chainID string) {
	packets := b.link.ConsumePackets(b.otherID(chainID), 1)
	for _, p := range packets {
		receiver := b.endpointFromID(chainID)
		sender := receiver.Counterparty
		ack, err := simibc.TryRecvPacket(sender, receiver, p.Packet)
		if err != nil {
			b.coordinator.Fatal("deliver")
		}
		b.link.AddAck(chainID, ack, p.Packet)
	}
}

func (b *Builder) deliverAcks(chainID string) {
	for _, ack := range b.link.ConsumeAcks(b.otherID(chainID), 999999) {
		err := simibc.TryRecvAck(b.endpointFromID(b.otherID(chainID)), b.endpointFromID(chainID), ack.Packet, ack.Ack)
		if err != nil {
			b.coordinator.Fatal("deliverAcks")
		}
	}
}

func (b *Builder) endBlock(chainID string) {
	c := b.coordinator.GetChain(chainID)

	ebRes := c.App.EndBlock(abci.RequestEndBlock{Height: c.CurrentHeader.Height})

	c.App.Commit()

	c.Vals = c.NextVals

	c.NextVals = ibctesting.ApplyValSetChanges(c.T, c.Vals, ebRes.ValidatorUpdates)

	c.LastHeader = c.CurrentTMClientHeader()
	// Store header to be used in UpdateClient
	b.clientHeaders[chainID] = append(b.clientHeaders[chainID], c.LastHeader)

	for _, e := range ebRes.Events {
		if e.Type == channeltypes.EventTypeSendPacket {
			packet, _ := channelkeeper.ReconstructPacketFromEvent(e)
			// Collect packets
			b.link.AddPacket(chainID, packet)
		}
	}

	// Commit packets emmitted up to this point
	b.link.Commit(chainID)

	newT := b.coordinator.CurrentTime.Add(b.initState.BlockSeconds).UTC()

	// increment the current header
	c.CurrentHeader = tmproto.Header{
		ChainID:            c.ChainID,
		Height:             c.App.LastBlockHeight() + 1,
		AppHash:            c.App.LastCommitID().Hash,
		Time:               newT,
		ValidatorsHash:     c.Vals.Hash(),
		NextValidatorsHash: c.NextVals.Hash(),
	}

	c.App.BeginBlock(abci.RequestBeginBlock{Header: c.CurrentHeader})
}

func (b *Builder) build() {

	b.createChains()
	b.createLink()
	b.setProviderSlashParams()
	b.addExtraProviderValidators()
	// Commit the additional validators
	b.coordinator.CommitBlock(b.chain(P))

	client, cons := b.getClientConsState()
	consumerGenesis := b.createConsumerGenesis(client, cons)
	b.consumerKeeper().InitGenesis(b.ctx(C), consumerGenesis)

	// Set the unbonding time on the consumer to the model value
	b.consumerKeeper().SetUnbondingPeriod(b.ctx(C), b.initState.UnbondingC)

	b.createPath()
	b.setProviderEndpointId()
	b.createProviderClient()

	// Create the Consumer chain ID mapping in the provider state
	b.providerKeeper().SetConsumerClientId(b.ctx(P), b.chain(C).ChainID, b.path.EndpointB.ClientID)

	// Handshake
	b.coordinator.CreateConnections(b.path)
	b.coordinator.CreateChannels(b.path)

	// Send an empty VSC packet from the provider to the consumer to finish
	// the handshake. This is necessary because the model starts from a
	// completely initialized state, with a completed handshake.
	b.sendEmptyVSCPacketToFinishHandshake()

	b.doTail()

}

func (b *Builder) doTail() {
	// Catch up consumer to have the same height and timestamp as provider
	b.endBlock(b.chainID(C))
	b.coordinator.CurrentTime = b.coordinator.CurrentTime.Add(time.Second * time.Duration(1)).UTC()
	b.beginBlock(b.chainID(C))
	b.endBlock(b.chainID(C))
	b.coordinator.CurrentTime = b.coordinator.CurrentTime.Add(time.Second * time.Duration(1)).UTC()
	b.beginBlock(b.chainID(C))
	b.endBlock(b.chainID(C))
	b.coordinator.CurrentTime = b.coordinator.CurrentTime.Add(time.Second * time.Duration(1)).UTC()
	b.mustBeginBlock[C] = true

	// Progress chains in unison, allowing first VSC to mature.
	for i := 0; i < 11; i++ {
		b.idempotentBeginBlock(P)
		b.endBlock(b.chainID(P))
		b.idempotentBeginBlock(C)
		b.endBlock(b.chainID(C))
		b.mustBeginBlock = map[string]bool{P: true, C: true}
		b.coordinator.CurrentTime = b.coordinator.CurrentTime.Add(b.initState.BlockSeconds).UTC()
	}

	b.idempotentBeginBlock(P)
	// Deliver outstanding ack
	b.deliverAcks(b.chainID(P))
	// Deliver the maturity from the first VSC (needed to complete handshake)
	b.deliver(b.chainID(P))

	for i := 0; i < 2; i++ {
		b.idempotentBeginBlock(P)
		b.endBlock(b.chainID(P))
		b.idempotentBeginBlock(C)
		b.deliverAcks(b.chainID(C))
		b.endBlock(b.chainID(C))
		b.mustBeginBlock = map[string]bool{P: true, C: true}
		b.coordinator.CurrentTime = b.coordinator.CurrentTime.Add(b.initState.BlockSeconds).UTC()
	}

	b.idempotentBeginBlock(P)
	b.idempotentBeginBlock(C)

	b.endBlock(b.chainID(P))
	b.endBlock(b.chainID(C))
	b.coordinator.CurrentTime = b.coordinator.CurrentTime.Add(b.initState.BlockSeconds).UTC()
	b.beginBlock(b.chainID(P))
	b.beginBlock(b.chainID(C))
	b.updateClient(b.chainID(P))
	b.updateClient(b.chainID(C))
}

// The state of the data returned is equivalent to the state of two chains
// after a full handshake, but the precise order of steps used to reach the
// state does not necessarily mimic the order of steps that happen in a
// live scenario.
func GetZeroState(suite *suite.Suite, initState InitState) (
	*ibctesting.Path, []sdk.ValAddress, int64, int64) {
	b := Builder{initState: initState, suite: suite}
	b.build()
	// Height of the last committed block (current header is not committed)
	heightLastCommitted := b.chain(P).CurrentHeader.Height - 1
	// Time of the last committed block (current header is not committed)
	timeLastCommitted := b.chain(P).CurrentHeader.Time.Add(-b.initState.BlockSeconds).Unix()
	return b.path, b.sdkValAddresses, heightLastCommitted, timeLastCommitted
}
