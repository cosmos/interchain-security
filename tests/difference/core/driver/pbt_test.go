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

// Model is a description of a rapid state machine for testing
type Model struct {
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

// ctx returns the sdk.Context for the chain
func (s *Model) ctx(chain string) sdk.Context {
	return s.chain(chain).GetContext()
}

func (s *Model) chainID(chain string) string {
	return map[string]string{P: ibctesting.GetChainID(0), C: ibctesting.GetChainID(1)}[chain]
}

// chain returns the TestChain for a given chain identifier
func (s *Model) chain(chain string) *ibctesting.TestChain {
	return map[string]*ibctesting.TestChain{P: s.providerChain(), C: s.consumerChain()}[chain]
}

func (s *Model) providerChain() *ibctesting.TestChain {
	return s.simibc.Chain(ibctesting.GetChainID(0))
}

func (s *Model) consumerChain() *ibctesting.TestChain {
	return s.simibc.Chain(ibctesting.GetChainID(1))
}

func (b *Model) providerStakingKeeper() stakingkeeper.Keeper {
	return b.providerChain().App.(*appProvider.App).StakingKeeper
}

func (b *Model) consumerKeeper() consumerkeeper.Keeper {
	return b.consumerChain().App.(*appConsumer.App).ConsumerKeeper
}

// height returns the height of the current header of chain
func (s *Model) height(chain string) int64 {
	return s.chain(chain).CurrentHeader.GetHeight()
}

// time returns the time of the current header of chain
func (s *Model) time(chain string) time.Time {
	return s.chain(chain).CurrentHeader.Time
}

// delegator retrieves the address for the delegator account
func (s *Model) delegator() sdk.AccAddress {
	return s.providerChain().SenderAccount.GetAddress()
}

// validator returns the address for the validator with id (ix) i
func (s *Model) validator(i int64) sdk.ValAddress {
	return s.valAddresses[i]
}

// delegate delegates amt tokens to validator val
func (s *Model) delegate(val int64, amt int64) {
	server := stakingkeeper.NewMsgServerImpl(s.providerStakingKeeper())
	coin := sdk.NewCoin(sdk.DefaultBondDenom, sdk.NewInt(amt))
	d := s.delegator()
	v := s.validator(val)
	msg := stakingtypes.NewMsgDelegate(d, v, coin)
	_, err := server.Delegate(sdk.WrapSDKContext(s.ctx(P)), msg)
	// There may or may not be an error, depending on the trace
	_ = err
}

// undelegate undelegates amt tokens from validator val
func (s *Model) undelegate(val int64, amt int64) {
	server := stakingkeeper.NewMsgServerImpl(s.providerStakingKeeper())
	coin := sdk.NewCoin(sdk.DefaultBondDenom, sdk.NewInt(amt))
	d := s.delegator()
	v := s.validator(val)
	msg := stakingtypes.NewMsgUndelegate(d, v, coin)
	_, err := server.Undelegate(sdk.WrapSDKContext(s.ctx(P)), msg)
	// There may or may not be an error, depending on the trace
	_ = err
}

// consumerSlash simulates a slash event occurring on the consumer chain.
// It can be for a downtime or doublesign.
func (s *Model) consumerSlash(val sdk.ConsAddress, h int64, isDowntime bool) {
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

// Init is an action for initializing  a Model instance.
func (m *Model) Init(t *rapid.T) {
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

	tee := m.time(P).Add(-initState.BlockSeconds)
	m.tLastTrustedHeader = map[string]time.Time{P: tee, C: tee}
	m.tLastCommit = map[string]time.Time{P: tee, C: tee}
}

func (m *Model) Cleanup() {
	// Keeping this line in seems to cause an error immediately
	// Not exactly sure when Rapid calls Cleanup

	// localT = nil // TODO: ????
}

// Check runs after every action and verifies that all required invariants hold.
func (m *Model) Check(t *rapid.T) {
	if 0 != 0 {
		t.Fatalf("wrong!")
	}
}

func (m *Model) Delegate(t *rapid.T) {
	val := rapid.Int64Range(0, 3).Draw(t, "val")
	amt := rapid.Int64Range(1000, 5000).Draw(t, "amt")
	m.delegate(val, amt)
}

func (m *Model) Undelegate(t *rapid.T) {
	val := rapid.Int64Range(0, 3).Draw(t, "val")
	amt := rapid.Int64Range(1000, 5000).Draw(t, "amt")
	m.undelegate(val, amt)
}

func (m *Model) ConsumerSlash(t *rapid.T) {
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

func (m *Model) updateClient(chain string) {
	other := C

	if chain == C {
		other = P
	}

	m.tLastTrustedHeader[chain] = m.tLastCommit[other]
	m.simibc.UpdateClient(m.chainID(chain))
}

func (m *Model) UpdateClient(t *rapid.T) {
	options := []string{P, C}
	chain := rapid.SampledFrom(options).Draw(t, "chain")
	m.updateClient(chain)
}

func (m *Model) Deliver(t *rapid.T) {
	options := []string{P, C}
	chain := rapid.SampledFrom(options).Draw(t, "chain")
	num := rapid.IntRange(0, 10).Draw(t, "num")
	m.updateClient(chain)
	// Deliver any outstanding acks
	m.simibc.DeliverAcks(m.chainID(chain), 999999)
	// Consume deliverable packets from the network
	m.simibc.DeliverPackets(m.chainID(chain), num)
}

func (m *Model) EndAndBeginBlock(t *rapid.T) {
	options := []string{P, C}
	chain := rapid.SampledFrom(options).Draw(t, "chain")

	valid := func() bool {
		tee := m.time(chain)
		teeLastTrusted := m.tLastTrustedHeader[chain]
		// chain time + block seconds < time last trusted header + trusting period
		willNotCauseClientExpiry := tee.Add(initState.BlockSeconds).Before(teeLastTrusted.Add(initState.Trusting))
		return willNotCauseClientExpiry
	}

	if valid() {
		m.tLastCommit[chain] = m.time(chain)
		m.simibc.EndAndBeginBlock(
			m.chainID(chain),
			initState.BlockSeconds,
			func() {
			})
	} else {
		// TODO: log something?
	}
}

// go test -v -timeout 10m -run Queue -rapid.checks=1000 -rapid.steps=1000
func TestPBT(t *testing.T) {
	localT = t
	rapid.Check(t, rapid.Run[*Model]())

	/*
	 See args prefixed with `rapid` in output of `go test -args -h`
	 -rapid.checks int
	 rapid: number of checks to perform (default 100)
	 -rapid.debug
	 rapid: debugging output
	 -rapid.debugvis
	 rapid: debugging visualization
	 -rapid.failfile string
	 rapid: fail file to use to reproduce test failure
	 -rapid.log
	 rapid: eager verbose output to stdout (to aid with unrecoverable test failures)
	 -rapid.nofailfile
	 rapid: do not write fail files on test failures
	 -rapid.seed uint
	 rapid: PRNG seed to start with (0 to use a random one)
	 -rapid.shrinktime duration
	 rapid: maximum time to spend on test case minimization (default 30s)
	 -rapid.steps int
	 rapid: number of state machine steps to perform (default 100)
	 -rapid.v
	 rapid: verbose output
	*/

}
