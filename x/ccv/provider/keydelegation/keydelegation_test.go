package keydelegation_test

import (
	"testing"

	keydelegation "github.com/cosmos/interchain-security/x/ccv/provider/keydelegation"
	"pgregory.net/rapid"
)

// Machine is a description of a rapid state machine for testing Queue
type Machine struct {
	kd    keydelegation.KeyDelegation // queue being tested
	state []int                       // model of the queue
}

// Init is an action for initializing  a queueMachine instance.
func (m *Machine) Init(t *rapid.T) {
	m.kd = keydelegation.MakeKeyDelegation()
	m.state = []int{}
}

// Get is a conditional action which removes an item from the queue.
func (m *Machine) Get(t *rapid.T) {
	if m.q.Size() == 0 {
		t.Skip("queue empty")
	}

	i := m.q.Get()
	if i != m.state[0] {
		t.Fatalf("got invalid value: %v vs expected %v", i, m.state[0])
	}
	m.state = m.state[1:]
}

// Put is a conditional action which adds an items to the queue.
func (m *Machine) SetForeignKey(t *rapid.T) {
	if m.q.Size() == m.n {
		t.Skip("queue full")
	}

	i := rapid.Int().Draw(t, "i")
	m.q.Put(i)
	m.state = append(m.state, i)
}

// Check runs after every action and verifies that all required invariants hold.
func (m *Machine) Check(t *rapid.T) {
	if 32 == 42 {
		t.Fatalf("error msg")
	}
}

// Rename to TestQueue(t *testing.T) to make an actual (failing) test.
func ExampleRun_keydelegation() {
	var t *testing.T
	rapid.Check(t, rapid.Run[*Machine]())
}
