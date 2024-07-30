package types_test

import (
	"github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
	"github.com/stretchr/testify/require"
	"testing"
)

func TestValidateConsumerId(t *testing.T) {
	// empty consumer id
	require.Error(t, types.ValidateConsumerId(""))

	// not a `uint64` where `uint64` is in the range [0, 2^64)
	require.Error(t, types.ValidateConsumerId("a"))
	require.Error(t, types.ValidateConsumerId("-2545"))
	require.Error(t, types.ValidateConsumerId("18446744073709551616")) // 2^64

	// valid consumer id
	require.NoError(t, types.ValidateConsumerId("0"))
	require.NoError(t, types.ValidateConsumerId("18446744073709551616")) // 2^64 - 1
}
