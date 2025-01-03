package types_test

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/cosmos/interchain-security/v6/x/ccv/types"
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
	require.NoError(t, types.ValidateConsumerId("18446744073709551615")) // 2^64 - 1
}

func TestValidateConnectionIdentifier(t *testing.T) {
	testCases := []struct {
		name    string
		connId  string
		expPass bool
	}{
		{
			name:    "valid connection ID",
			connId:  "connection-0",
			expPass: true,
		},
		{
			name:    "valid empty connection ID",
			connId:  "",
			expPass: true,
		},
		{
			name:    "valid empty (multiple spaces) connection ID",
			connId:  "  ",
			expPass: true,
		},
		{
			name:    "invalid connection ID with /",
			connId:  "invalid-connection-id/",
			expPass: false,
		},
		{
			name:    "invalid connection ID with special characters",
			connId:  "connection-@#",
			expPass: false,
		},
		{
			name:    "invalid connection ID with spaces",
			connId:  "connection id",
			expPass: false,
		},
	}

	for _, tc := range testCases {
		err := types.ValidateConnectionIdentifier(tc.connId)
		if tc.expPass {
			require.NoError(t, err, "valid case: '%s' should not return error. got %w", tc.name, err)
		} else {
			require.Error(t, err, "invalid case: '%s' must return error but got none", tc.name)
		}
	}
}
