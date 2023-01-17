package core

import (
	"testing"
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingkeeper "github.com/cosmos/cosmos-sdk/x/staking/keeper"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	appConsumer "github.com/cosmos/interchain-security/app/consumer"
	appProvider "github.com/cosmos/interchain-security/app/provider"
	ibctestingcore "github.com/cosmos/interchain-security/legacy_ibc_testing/core"
	ibctesting "github.com/cosmos/interchain-security/legacy_ibc_testing/testing"
	"github.com/cosmos/interchain-security/tests/property-based/core/setup"
	simibc "github.com/cosmos/interchain-security/testutil/simibc"
	consumerkeeper "github.com/cosmos/interchain-security/x/ccv/consumer/keeper"
	"github.com/tendermint/tendermint/libs/bytes"
	"pgregory.net/rapid"
)

const P = setup.P
const C = setup.C

/*
The rapid library does not currently provide a way to inject custom state into
the harness (Model, in this case). We need a handle to a testing.T in the harness
to be able to use ibc-go/testing::TestChain. Therefore, we set a global as a hack.
See https://github.com/flyingmutant/rapid/issues/48
*/
var localT *testing.T

// Harness is a description of a rapid state machine for testing
type Harness struct {
	// simulate a relayed path
	simibc simibc.RelayedPath

	// keep around validators for easy access
	valAddresses []sdk.ValAddress

	// Need initial chain height to calculate possible
	// infraction heights on consumer chain
	// Note that provider and consumer have the same
	// initial chain height.
	initialChainHeight int64

	didSlash           []bool
	tLastTrustedHeader map[string]time.Time
	tLastCommit        map[string]time.Time
	trustDuration      time.Duration

	providerValsets [][]int64
}

/////////////////////////////////////////////////////////////////////////////////////////
// HELPERS BELOW

func (s *Harness) ctx(chain string) sdk.Context {
	return s.chain(chain).GetContext()
}

func (s *Harness) chainID(chain string) string {
	return map[string]string{P: ibctesting.GetChainID(0), C: ibctesting.GetChainID(1)}[chain]
}

func (s *Harness) chain(chain string) *ibctesting.TestChain {
	return map[string]*ibctesting.TestChain{P: s.providerChain(), C: s.consumerChain()}[chain]
}

func (s *Harness) providerChain() *ibctesting.TestChain {
	return s.simibc.Chain(ibctesting.GetChainID(0))
}

func (s *Harness) consumerChain() *ibctesting.TestChain {
	return s.simibc.Chain(ibctesting.GetChainID(1))
}

func (b *Harness) providerStakingKeeper() stakingkeeper.Keeper {
	return b.providerChain().App.(*appProvider.App).StakingKeeper
}

func (b *Harness) consumerKeeper() consumerkeeper.Keeper {
	return b.consumerChain().App.(*appConsumer.App).ConsumerKeeper
}

func (s *Harness) height(chain string) int64 {
	return s.chain(chain).CurrentHeader.GetHeight()
}

func (s *Harness) time(chain string) time.Time {
	return s.chain(chain).CurrentHeader.Time
}

func (s *Harness) delegator() sdk.AccAddress {
	return s.providerChain().SenderAccount.GetAddress()
}

func (s *Harness) validator(i int64) sdk.ValAddress {
	return s.valAddresses[i]
}

func (s *Harness) delegate(val int64, amt int64) {
	server := stakingkeeper.NewMsgServerImpl(s.providerStakingKeeper())
	coin := sdk.NewCoin(sdk.DefaultBondDenom, sdk.NewInt(amt))
	d := s.delegator()
	v := s.validator(val)
	msg := stakingtypes.NewMsgDelegate(d, v, coin)
	_, err := server.Delegate(sdk.WrapSDKContext(s.ctx(P)), msg)
	// There may or may not be an error because the delegator might not have enough funds
	_ = err
}

func (s *Harness) undelegate(val int64, amt int64) {
	server := stakingkeeper.NewMsgServerImpl(s.providerStakingKeeper())
	coin := sdk.NewCoin(sdk.DefaultBondDenom, sdk.NewInt(amt))
	d := s.delegator()
	v := s.validator(val)
	msg := stakingtypes.NewMsgUndelegate(d, v, coin)
	_, err := server.Undelegate(sdk.WrapSDKContext(s.ctx(P)), msg)
	// There may or may not be an error because the delegator might not have enough shares
	_ = err
}

func (s *Harness) consumerSlash(val sdk.ConsAddress, h int64, isDowntime bool) {
	kind := stakingtypes.DoubleSign
	if isDowntime {
		kind = stakingtypes.Downtime
	}
	ctx := s.ctx(C)
	before := len(ctx.EventManager().Events())
	s.consumerKeeper().Slash(ctx, val, h, 0, sdk.Dec{}, kind)
	// consumer module emits packets on slash, so these must be collected.
	evts := ctx.EventManager().ABCIEvents()
	for _, e := range evts[before:] {
		if e.Type == channeltypes.EventTypeSendPacket {
			packet, _ := ibctestingcore.ReconstructPacketFromEvent(e)
			s.simibc.Link.AddPacket(s.chainID(C), packet)
		}
	}
}

func (m *Harness) updateClient(chain string) {
	other := C

	if chain == C {
		other = P
	}

	m.tLastTrustedHeader[chain] = m.tLastCommit[other]
	m.simibc.UpdateClient(m.chainID(chain))
}

func (m Harness) saveProviderValset() {
	m.providerStakingKeeper().IterateLastValidatorPowers(m.ctx(P), func(addr sdk.ValAddress, power int64) bool {
		powers := make([]int64, len(m.valAddresses))
		for i, valAddr := range m.valAddresses {
			if valAddr.Equals(addr) {
				powers[i] = power
			}
		}
		m.providerValsets = append(m.providerValsets, powers)
		return false // Do not break early
	})
}

/////////////////////////////////////////////////////////////////////////////////////////
// PROPERTIES / INVARIANTS BELOW

func (m *Harness) validatorSetReplication() bool {

	getConsumerAddressToValidatorMap := func() map[string]int {
		ret := make(map[string]int)
		for i, valAddr := range m.valAddresses {
			valP, found := m.providerStakingKeeper().GetValidator(m.ctx(P), valAddr)
			if !found {
				panic("very bad!")
			}
			pk, err := valP.ConsPubKey()
			if err != nil {
				panic("also very bad!")
			}
			addrP := pk.Address()
			ret[addrP.String()] = i
		}
		return ret
	}

	special := getConsumerAddressToValidatorMap()

	valsC := m.consumerKeeper().GetAllCCValidator(m.ctx(C))
	// Build a list of powers for the consumer validator set where the
	// validators are in the same order as they are in the provider set.
	valsetC := make([]int64, len(m.valAddresses))
	for _, valC := range valsC {
		// addrC is the result of doing x.Address() on an sdktypes.PubKey
		addrC := valC.GetAddress()
		// Gymnastics needed to see through the various type systems
		valP := special[bytes.HexBytes(addrC).String()]
		// We found the power
		valsetC[valP] = valC.GetPower()
	}
	good := false
	// See if any of the provider valsets match the consumer valset
	for _, valsetP := range m.providerValsets {
		innerGood := true
		for i := 0; i < len(m.valAddresses); i++ {
			if valsetP[i] != valsetC[i] {
				// No match, try the next one
				innerGood = false
				break
			}
		}
		if innerGood {
			good = true
			break
		}
	}
	return good
}

/////////////////////////////////////////////////////////////////////////////////////////
// RAPID METHODS BELOW

// Init is run by rapid first, to setup a model instance.
func (m *Harness) Init(t *rapid.T) {
	z := setup.GetZeroState(localT)
	m.valAddresses = z.Addrs
	m.initialChainHeight = z.HeightLastCommit
	m.simibc = simibc.MakeRelayedPath(localT, z.Path)
	m.trustDuration = z.TrustDuration

	m.didSlash = make([]bool, len(m.valAddresses))

	m.tLastTrustedHeader = map[string]time.Time{P: z.TimeLastCommit, C: z.TimeLastCommit}
	m.tLastCommit = map[string]time.Time{P: z.TimeLastCommit, C: z.TimeLastCommit}

	m.providerValsets = [][]int64{}
	m.saveProviderValset() // Save the initial val set
}

func (m *Harness) Delegate(t *rapid.T) {
	val := rapid.Int64Range(0, 3).Draw(t, "val")
	amt := rapid.Int64Range(1000, 5000).Draw(t, "amt")
	m.delegate(val, amt)
}

func (m *Harness) Undelegate(t *rapid.T) {
	val := rapid.Int64Range(0, 3).Draw(t, "val")
	amt := rapid.Int64Range(1000, 5000).Draw(t, "amt")
	m.undelegate(val, amt)
}

func (m *Harness) ConsumerSlash(t *rapid.T) {
	val := rapid.Int64Range(0, 3).Draw(t, "val")

	valid := func() bool {
		numNotSlashed := 0
		for _, slashed := range m.didSlash {
			if !slashed {
				numNotSlashed += 1
			}
		}
		alreadySlashed := m.didSlash[val]
		willNotJailAllValidators :=
			(1 < numNotSlashed) || alreadySlashed
		return willNotJailAllValidators
	}

	if !valid() {
		return
	}

	cons := sdk.ConsAddress(m.valAddresses[val])

	lower := m.initialChainHeight
	currH := m.height(C)
	// TODO: can infraction be for current height?
	upper := currH - 1 //
	if upper < lower {
		lower = upper
	}
	h := rapid.Int64Range(lower, upper).Draw(t, "h")

	isDowntime := rapid.Bool().Draw(t, "isDowntime")

	m.didSlash[val] = true
	m.consumerSlash(cons, h, isDowntime)
}

func (m *Harness) UpdateClientAction(t *rapid.T) {
	options := []string{P, C}
	chain := rapid.SampledFrom(options).Draw(t, "chain")
	m.updateClient(chain)
}

func (m *Harness) DeliverAction(t *rapid.T) {
	options := []string{P, C}
	chain := rapid.SampledFrom(options).Draw(t, "chain")
	num := rapid.IntRange(0, 10).Draw(t, "num")
	m.updateClient(chain)
	// Deliver any outstanding acks
	m.simibc.DeliverAcks(m.chainID(chain), 999999)
	// Consume deliverable packets from the network
	m.simibc.DeliverPackets(m.chainID(chain), num)
}

func (m *Harness) EndAndBeginBlockAction(t *rapid.T) {
	options := []string{P, C}
	chain := rapid.SampledFrom(options).Draw(t, "chain")

	// The number of seconds to between the current block
	// and the header of the next block.
	dtNumSeconds := rapid.IntRange(1, 10).Draw(t, "dt")
	dt := time.Duration(dtNumSeconds) * time.Second

	valid := func() bool {
		tee := m.time(chain)
		teeLastTrusted := m.tLastTrustedHeader[chain]
		// chain time + block seconds < time last trusted header + trusting period
		willNotCauseClientExpiry := tee.Add(dt).Before(teeLastTrusted.Add(m.trustDuration))
		return willNotCauseClientExpiry
	}

	if valid() {
		m.tLastCommit[chain] = m.time(chain)
		m.simibc.EndAndBeginBlock(
			m.chainID(chain),
			dt,
			func() {
				if chain == P {
					m.saveProviderValset()
				}
			})
	}
	// TODO: log something? in else case?
}

// Check runs after every action and verifies that all required invariants hold.
func (m *Harness) Check(t *rapid.T) {
	// fatal if bad
	if !m.validatorSetReplication() {
		t.Fatal("validator set replication failed")
	}
}

// Cleanup is deffered by rapid and can be used for freeing resource
func (m *Harness) Cleanup() {
}

// go test -v -timeout 10m -run PropertyBased -rapid.checks=1000 -rapid.steps=1000 -rapid.log
// `checks` is the number of new models to run steps for
// `steps` is the number of actions to run for each model
// See `go test -args -h` for a full list of arguments
func TestPropertyBased(t *testing.T) {
	localT = t
	rapid.Check(t, rapid.Run[*Harness]())
}
