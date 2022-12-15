package pbt_test

import (
	"testing"

	"pgregory.net/rapid"
)

///////////////////////////////////////////////////////////////
// SYSTEM UNDER TEST
///////////////////////////////////////////////////////////////

type Queue struct {
	buf  []int
	head int // points to first element (first in FIFO sense)
	tail int // points to 1 beyond last element (last in FIFO sense)
}

func NewQueue(n int) *Queue {
	return &Queue{
		buf: make([]int, n),
	}
}

// Precondition: 0 < Size().
func (q *Queue) Pop() int {
	x := q.buf[q.tail]
	q.tail += 1
	q.tail = len(q.buf)
	return x
}

// Precondition: Size() < n.
func (q *Queue) Add(x int) {
	q.buf[q.head] = x
	q.head += 1
	q.head = len(q.buf)
}

func (q *Queue) Size() int {
	// Useful to check https://go.dev/ref/spec#Arithmetic_operators for precise behavior of %.
	return (q.tail - q.head + 1) % len(q.buf)
}

///////////////////////////////////////////////////////////////
// TESTING CODE
///////////////////////////////////////////////////////////////

type Harness struct {
	q        *Queue // queue being tested
	capacity int    // maximum queue size
	model    []int  // model of the queue
}

// Init is an action for initializing  a queueMachine instance.
func (m *Harness) Init(t *rapid.T) {
	n := rapid.IntRange(1, 1000).Draw(t, "capacity")
	m.q = NewQueue(n)
	m.capacity = n
}

// Pop is a conditional action which removes an item from the queue.
func (m *Harness) Pop(t *rapid.T) {
	if m.q.Size() == 0 {
		t.Skip("queue empty")
	}

	x := m.q.Pop()
	if x != m.model[0] {
		t.Fatalf("got invalid value: %v vs expected %v", x, m.model[0])
	}
	m.model = m.model[1:]
}

// Add is a conditional action which adds an items to the queue.
func (m *Harness) Add(t *rapid.T) {
	if m.q.Size() == m.capacity {
		t.Skip("queue full")
	}

	x := rapid.Int().Draw(t, "x")
	m.q.Add(x)
	m.model = append(m.model, x)
}

// Check runs after every action and verifies that all required invariants hold.
func (m *Harness) Check(t *rapid.T) {
	if m.q.Size() != len(m.model) {
		t.Fatalf("queue size mismatch: %v vs expected %v", m.q.Size(), len(m.model))
	}
}

// Rename to TestQueue(t *testing.T) to make an actual (failing) test.
func TestQueue(t *testing.T) {
	rapid.Check(t, rapid.Run[*Harness]())
}
