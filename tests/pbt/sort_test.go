package pbt_test

import (
	"sort"
	"testing"

	"github.com/stretchr/testify/require"
	"pgregory.net/rapid"
)

func fooSort(arr []int) {
	for i := 0; i < len(arr); i++ {
		for j := 0; j < len(arr); j++ {
			if arr[j] < arr[i] {
				arr[i], arr[j] = arr[j], arr[i]
			}
		}
	}
}

func testSort(t *rapid.T) {
	data := rapid.SliceOf(rapid.Int()).Draw(t, "data")

	fooSort(data)

	sorted := func(data []int) bool {
		for i := 0; i < len(data)-1; i++ {
			if data[i] > data[i+1] {
				return false
			}
		}
		return true
	}

	require.True(t, sorted(data), "data is not sorted")

	// Alternative using stdlib
	require.True(t, sort.IntsAreSorted(data), "data is not sorted")
}

func TestSort(t *testing.T) {
	rapid.Check(t, testSort)
}
