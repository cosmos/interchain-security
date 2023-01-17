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
	simibc "github.com/cosmos/interchain-security/testutil/simibc"
	consumerkeeper "github.com/cosmos/interchain-security/x/ccv/consumer/keeper"
	"pgregory.net/rapid"
)

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
	// initial chain height
	initialChainHeight int64

	didSlash           []bool
	tLastTrustedHeader map[string]time.Time
	tLastCommit        map[string]time.Time
}

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

// Init is an action for initializing  a Model instance.
func (m *Harness) Init(t *rapid.T) {

	state := initState
	path, valAddresses, initialChainHeight, _ := GetZeroState(localT, state)
	m.valAddresses = valAddresses
	m.initialChainHeight = initialChainHeight
	m.simibc = simibc.MakeRelayedPath(localT, path)

	//////////////////////////////////////////////////////////////////////
	m.didSlash = []bool{false, false, false, false}

	// I THINK for this value, we can use the time of the last commit
	// because the last steps of Setup() are to end block on both chains
	// then begin a new block and update latest client

	tee := m.time(P).Add(-initState.BlockInterval)
	m.tLastTrustedHeader = map[string]time.Time{P: tee, C: tee}
	m.tLastCommit = map[string]time.Time{P: tee, C: tee}
}

func (m *Harness) Cleanup() {
	// Keeping this line in seems to cause an error immediately
	// Not exactly sure when Rapid calls Cleanup

	// localT = nil // TODO: ????
}

// Check runs after every action and verifies that all required invariants hold.
func (m *Harness) Check(t *rapid.T) {
	// fatal if bad
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

	// cons := m.consAddr(val)
	cons := sdk.ConsAddress(m.valAddresses[val])

	// h := rapid.Int64Range(0, 100).Draw(t, "h") // TODO: proper range!
	currH := m.height(C)
	lower := m.initialChainHeight
	upper := currH - 1
	if upper < lower {
		lower = upper
	}
	h := rapid.Int64Range(lower, upper).Draw(t, "h") // TODO: check bounds!

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

	valid := func() bool {
		tee := m.time(chain)
		teeLastTrusted := m.tLastTrustedHeader[chain]
		// chain time + block seconds < time last trusted header + trusting period
		willNotCauseClientExpiry := tee.Add(initState.BlockInterval).Before(teeLastTrusted.Add(initState.Trusting))
		return willNotCauseClientExpiry
	}

	if valid() {
		m.tLastCommit[chain] = m.time(chain)
		m.simibc.EndAndBeginBlock(
			m.chainID(chain),
			initState.BlockInterval,
			func() {
			})
	}
	// TODO: log something? in else case?
}

// go test -v -timeout 10m -run PropertyBased -rapid.checks=1000 -rapid.steps=1000 -rapid.log
// `checks` is the number of new models to run steps for
// `steps` is the number of actions to run for each model
// See `go test -args -h` for a full list of arguments
func TestPropertyBased(t *testing.T) {
	localT = t
	rapid.Check(t, rapid.Run[*Harness]())
}
