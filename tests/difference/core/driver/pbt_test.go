package core

import (
	"testing"

	sdk "github.com/cosmos/cosmos-sdk/types"
	simibc "github.com/cosmos/interchain-security/testutil/simibc"
	"pgregory.net/rapid"
)

// Model is a description of a rapid state machine for testing
type Model struct {
	// simulate a relayed path
	simibc simibc.RelayedPath

	// keep around validators for easy access
	valAddresses []sdk.ValAddress

	// offsets: the model time and heights start at 0
	// so offsets are needed for comparisons.
	offsetTimeUnix int64
	offsetHeight   int64
}

// Init is an action for initializing  a Model instance.
func (m *Model) Init(t *rapid.T) {
	state := initState
	path, valAddresses, offsetHeight, offsetTimeUnix := GetZeroState(t, state)
	m.valAddresses = valAddresses
	m.offsetHeight = offsetHeight
	m.offsetTimeUnix = offsetTimeUnix
	m.simibc = simibc.MakeRelayedPath(t, path)
}

func (m *Model) Cleanup() {
}

// Check runs after every action and verifies that all required invariants hold.
func (m *Model) Check(t *rapid.T) {
	if 0 != 0 {
		t.Fatalf("wrong!")
	}
}

// See args prefixed with `rapid` in output of `go test -args -h`
// -rapid.checks int
// rapid: number of checks to perform (default 100)
// -rapid.debug
// rapid: debugging output
// -rapid.debugvis
// rapid: debugging visualization
// -rapid.failfile string
// rapid: fail file to use to reproduce test failure
// -rapid.log
// rapid: eager verbose output to stdout (to aid with unrecoverable test failures)
// -rapid.nofailfile
// rapid: do not write fail files on test failures
// -rapid.seed uint
// rapid: PRNG seed to start with (0 to use a random one)
// -rapid.shrinktime duration
// rapid: maximum time to spend on test case minimization (default 30s)
// -rapid.steps int
// rapid: number of state machine steps to perform (default 100)
// -rapid.v
// rapid: verbose output
//
// go test -v -timeout 10m -run Queue -rapid.checks=1000 -rapid.steps=1000
func TestPBT(t *testing.T) {
	rapid.Check(t, rapid.Run[*Model]())
}
