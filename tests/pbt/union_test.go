package pbt_test

import (
	"testing"

	"github.com/stretchr/testify/require"
	"pgregory.net/rapid"
)

func fooSetUnion(a []int, b []int) []int {
	ret := []int{}
	for _, x := range a {
		ret = append(ret, x)
	}
	for _, x := range b {
		alreadyPresent := false
		for _, y := range ret {
			if y == x {
				alreadyPresent = true
			}
		}
		if !alreadyPresent {
			ret = append(ret, x)
		}
	}
	return ret
}

func testSetUnion(t *rapid.T) {
	setA := rapid.SliceOfDistinct(rapid.Int(), func(x int) int { return x }).Draw(t, "setA")
	setB := rapid.SliceOfDistinct(rapid.Int(), func(x int) int { return x }).Draw(t, "setB")
	setC := fooSetUnion(setA, setB)

	allSinC := func(S []int) bool {
		for _, x := range S {
			good := false
			for _, y := range setC {
				if x == y {
					good = true
				}
			}
			if !good {
				return false
			}
		}
		return true
	}

	allCinAorB := func() bool {
		for _, x := range setC {
			good := false
			for _, y := range setA {
				if x == y {
					good = true
				}
			}
			for _, y := range setB {
				if x == y {
					good = true
				}
			}
			if !good {
				return false
			}
		}
		return true
	}

	noDuplicates := func() bool {
		seen := map[int]bool{}
		for _, x := range setC {
			if _, ok := seen[x]; ok {
				return false
			}
			seen[x] = true
		}
		return true
	}

	require.True(t, allSinC(setA), "not all elements of setA are in set C")
	require.True(t, allSinC(setB), "not all elements of setB are in set C")
	// Exercise: adapt the function allSinC to accept a set 'C' as argument
	//           and use the modified function instead of allCinAorB
	require.True(t, allCinAorB(), "not all elements of setC are in set A or set B")
	require.True(t, noDuplicates(), "set C contains duplicate elements")
}

func TestSetUnion(t *testing.T) {
	rapid.Check(t, testSetUnion)
}
