package pbt_test

import (
	"testing"

	"github.com/stretchr/testify/require"
	"pgregory.net/rapid"
)

func fooSetUnion(a []int, b []int) []int {
	ret := []int{}
	return ret
}

func testSetUnion(t *rapid.T) {
	setA := rapid.SliceOfDistinct(rapid.Int(), func(x int) int { return x }).Draw(t, "setA")
	setB := rapid.SliceOfDistinct(rapid.Int(), func(x int) int { return x }).Draw(t, "setB")
	setC := fooSetUnion(setA, setB)
	// Add property checks here..
	_, _, _ = setA, setB, setC
	require.True(t, false)
}

func TestSetUnion(t *testing.T) {
	rapid.Check(t, testSetUnion)
}
