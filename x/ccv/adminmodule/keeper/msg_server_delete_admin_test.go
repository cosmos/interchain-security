package keeper_test

import (
	"testing"

	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/interchain-security/x/ccv/adminmodule/types"
	"github.com/stretchr/testify/require"
)

func TestDeleteAdmin(t *testing.T) {
	// queryClient := suite.queryClient
	// keeper, ctx := setupKeeper(t)
	msgServer, ctx, keeper := setupMsgServer(t)

	var req *types.QueryAdminsRequest

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
				initialAdmins := []string{"cosmos1zwlgx3kxcykszdxrk2gvrrfzchlqzfc59kx3p0", "cosmosTeStgx3kxcykszdxrk2gvrrfzchlqzfc59kx4s8"}

				adminToDelete := ""

				initErr := InitTestAdmins(keeper, sdk.UnwrapSDKContext(ctx), initialAdmins)
				if initErr != nil {
					t.Errorf("Error initializing admins: %s\n", initErr)
				}
				deleteAdminMsg := &types.MsgDeleteAdmin{Creator: initialAdmins[0], Admin: adminToDelete}

				// Actual delete admin msg function
				_, err := msgServer.DeleteAdmin(ctx, deleteAdminMsg)
				require.Error(t, err)
			},
			false,
			[]string{"cosmos1zwlgx3kxcykszdxrk2gvrrfzchlqzfc59kx3p0", "cosmosTeStgx3kxcykszdxrk2gvrrfzchlqzfc59kx4s8"},
		},
		{
			"non existent admin request",
			func() {
				req = &types.QueryAdminsRequest{}
				initialAdmins := []string{"cosmos1zwlgx3kxcykszdxrk2gvrrfzchlqzfc59kx3p0", "cosmosTeStgx3kxcykszdxrk2gvrrfzchlqzfc59kx4s8"}

				adminToDelete := "cosmosnonexistentkszdxrk2gvrrfzchlqzfc59kx123"

				initErr := InitTestAdmins(keeper, sdk.UnwrapSDKContext(ctx), initialAdmins)
				if initErr != nil {
					t.Errorf("Error initializing admins: %s\n", initErr)
				}
				deleteAdminMsg := &types.MsgDeleteAdmin{Creator: initialAdmins[0], Admin: adminToDelete}

				// Actual delete admin msg function
				_, err := msgServer.DeleteAdmin(ctx, deleteAdminMsg)
				require.Error(t, err)
			},
			false,
			[]string{"cosmos1zwlgx3kxcykszdxrk2gvrrfzchlqzfc59kx3p0", "cosmosTeStgx3kxcykszdxrk2gvrrfzchlqzfc59kx4s8"},
		},
		{
			"valid request",
			func() {
				req = &types.QueryAdminsRequest{}
				initialAdmins := []string{"cosmos1zwlgx3kxcykszdxrk2gvrrfzchlqzfc59kx3p0", "cosmosTeStgx3kxcykszdxrk2gvrrfzchlqzfc59kx4s8"}

				adminToDelete := initialAdmins[1]

				initErr := InitTestAdmins(keeper, sdk.UnwrapSDKContext(ctx), initialAdmins)
				if initErr != nil {
					t.Errorf("Error initializing admins: %s\n", initErr)
				}

				deleteAdminMsg := &types.MsgDeleteAdmin{Creator: initialAdmins[0], Admin: adminToDelete}

				// Actual add admin msg function
				_, err := msgServer.DeleteAdmin(ctx, deleteAdminMsg)
				require.NoError(t, err)
			},
			true,
			[]string{"cosmos1zwlgx3kxcykszdxrk2gvrrfzchlqzfc59kx3p0"},
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
