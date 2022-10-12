package keeper_test

import (
	"testing"

	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/interchain-security/x/ccv/adminmodule/types"
	"github.com/stretchr/testify/require"
)

func TestAddAdmin(t *testing.T) {
	// queryClient := suite.queryClient
	// keeper, ctx := setupKeeper(t)
	msgServer, ctx, keeper := setupMsgServer(t)

	var (
		req          *types.QueryAdminsRequest
		initialAdmin = "cosmos1zwlgx3kxcykszdxrk2gvrrfzchlqzfc59kx3p0"
	)

	testCases := []struct {
		msg     string
		test    func()
		expPass bool
		expRes  []string
	}{
		{
			"empty admin address",
			func() {
				req = &types.QueryAdminsRequest{}

				initErr := InitTestAdmins(keeper, sdk.UnwrapSDKContext(ctx), []string{initialAdmin})
				if initErr != nil {
					t.Errorf("Error initializing admins: %s\n", initErr)
				}

				newAdmin := ""
				newAdminMsg := &types.MsgAddAdmin{Creator: initialAdmin, Admin: newAdmin}
				err := newAdminMsg.ValidateBasic()
				require.Error(t, err)
			},
			false,
			[]string{"cosmos1zwlgx3kxcykszdxrk2gvrrfzchlqzfc59kx3p0"},
		},
		{
			"invalid admin address",
			func() {
				req = &types.QueryAdminsRequest{}

				initErr := InitTestAdmins(keeper, sdk.UnwrapSDKContext(ctx), []string{initialAdmin})
				if initErr != nil {
					t.Errorf("Error initializing admins: %s\n", initErr)
				}

				newAdmin := "invalid admin"
				newAdminMsg := &types.MsgAddAdmin{Creator: initialAdmin, Admin: newAdmin}
				err := newAdminMsg.ValidateBasic()
				require.Error(t, err)
			},
			false,
			[]string{"cosmos1zwlgx3kxcykszdxrk2gvrrfzchlqzfc59kx3p0"},
		},
		{
			"valid request",
			func() {
				req = &types.QueryAdminsRequest{}

				initErr := InitTestAdmins(keeper, sdk.UnwrapSDKContext(ctx), []string{initialAdmin})
				if initErr != nil {
					t.Errorf("Error initializing admins: %s\n", initErr)
				}

				newAdmin := "cosmosTeStgx3kxcykszdxrk2gvrrfzchlqzfc59kx4s8"
				newAdminMsg := &types.MsgAddAdmin{Creator: initialAdmin, Admin: newAdmin}

				// Actual add admin msg function
				_, err := msgServer.AddAdmin(ctx, newAdminMsg)
				require.NoError(t, err)
			},
			true,
			[]string{"cosmos1zwlgx3kxcykszdxrk2gvrrfzchlqzfc59kx3p0", "cosmosTeStgx3kxcykszdxrk2gvrrfzchlqzfc59kx4s8"},
		},
	}

	for _, testCase := range testCases {
		t.Logf("Case %s", testCase.msg)
		testCase.test()

		admins, _ := keeper.Admins(ctx, req)
		t.Log(testCase.expRes, admins.GetAdmins())
		require.Equal(t, testCase.expRes, admins.GetAdmins())
	}
}
