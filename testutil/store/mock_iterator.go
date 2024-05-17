package store

// MockIterator is a mock implementation of Iterator that simply iterates an underlying slice.
type MockIterator struct {
	keys   [][]byte
	values [][]byte

	curIndex int
}

func (MockIterator) Domain() ([]byte, []byte) {
	panic("not implemented")
}

func (m MockIterator) Valid() bool {
	return m.curIndex < len(m.keys)
}

func (m *MockIterator) Next() {
	m.curIndex++
}

func (m MockIterator) Key() []byte {
	return m.keys[m.curIndex]
}

func (m MockIterator) Value() []byte {
	return m.values[m.curIndex]
}

func (m MockIterator) Error() error {
	panic("not implemented")
}

func (m MockIterator) Close() error {
	return nil
}

// NewMockIterator creates a new MockIterator.
func NewMockIterator(
	keys [][]byte, values [][]byte,
) *MockIterator {
	return &MockIterator{
		keys:     keys,
		values:   values,
		curIndex: 0,
	}
}
