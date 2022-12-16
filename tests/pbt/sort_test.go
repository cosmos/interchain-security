package pbt_test

import (
	"sort"
	"testing"

	"github.com/stretchr/testify/require"
	"pgregory.net/rapid"
)

func fooSort(arr []int) {
	for i := 0; i < len(arr); i++ {
		for j := i; j < len(arr); j++ {
			if arr[j] < arr[i] {
				arr[i], arr[j] = arr[j], arr[i]
			}
		}
	}
}

func testSort(t *rapid.T) {

	data := rapid.SliceOf(rapid.Int()).Draw(t, "data")
	copy := []int{}
	copy = append(copy, data...)

	fooSort(data)

	sorted := func() bool {
		for i := 0; i < len(data)-1; i++ {
			if data[i] > data[i+1] {
				return false
			}
		}
		return true
	}

	identicalElements := func() bool {
		cntData := make(map[int]int)
		cntCopy := make(map[int]int)
		for _, x := range data {
			cntData[x]++
		}
		for _, x := range copy {
			cntCopy[x]++
		}
		for x, cnt := range cntCopy {
			if cntData[x] != cnt {
				return false
			}
		}
		for x, cnt := range cntData {
			if cntCopy[x] != cnt {
				return false
			}
		}
		return true
	}

	require.True(t, sorted(), "data is not sorted")
	require.True(t, identicalElements(), "data is not sorted")

	// Alternative using stdlib
	require.True(t, sort.IntsAreSorted(data), "data is not sorted")
}

func TestSort(t *testing.T) {
	rapid.Check(t, testSort)
}
