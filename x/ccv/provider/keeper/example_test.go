package keeper_test

import (
	"testing"

	"pgregory.net/rapid"
)

// Queue implements integer queue with a fixed maximum size.
type Queue struct {
	buf []int
	in  int
	out int
}

func NewQueue(n int) *Queue {
	return &Queue{
		buf: make([]int, n+1),
	}
}

// Precondition: Size() > 0.
func (q *Queue) Get() int {
	i := q.buf[q.out]
	q.out = (q.out + 1) % len(q.buf)
	return i
}

// Precondition: Size() < n.
func (q *Queue) Put(i int) {
	q.buf[q.in] = i
	q.in = (q.in + 1) % len(q.buf)
}

func (q *Queue) Size() int {
	return (q.in - q.out) % len(q.buf)
}

// queueMachine is a description of a rapid state machine for testing Queue
type queueMachine struct {
	q     *Queue // queue being tested
	n     int    // maximum queue size
	state []int  // model of the queue
}

// Init is an action for initializing  a queueMachine instance.
func (m *queueMachine) Init(t *rapid.T) {
	n := rapid.IntRange(1, 1000).Draw(t, "n")
	m.q = NewQueue(n)
	m.n = n
}

// Get is a conditional action which removes an item from the queue.
func (m *queueMachine) Get(t *rapid.T) {
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
func (m *queueMachine) Put(t *rapid.T) {
	if m.q.Size() == m.n {
		t.Skip("queue full")
	}

	i := rapid.Int().Draw(t, "i")
	m.q.Put(i)
	m.state = append(m.state, i)
}

// Check runs after every action and verifies that all required invariants hold.
func (m *queueMachine) Check(t *rapid.T) {
	if m.q.Size() != len(m.state) {
		t.Fatalf("queue size mismatch: %v vs expected %v", m.q.Size(), len(m.state))
	}
}

// Rename to TestQueue(t *testing.T) to make an actual (failing) test.
func ExampleRun_queue() {
	var t *testing.T
	rapid.Check(t, rapid.Run[*queueMachine]())
}
