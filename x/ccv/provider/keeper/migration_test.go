package keeper_test

import (
	"testing"

	testutil "github.com/cosmos/interchain-security/v3/testutil/keeper"
)

func TestMigrate2To3(t *testing.T) {
	consumerKeeper, ctx, ctrl, _ := testutil.GetProviderKeeperAndCtx(t, testutil.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	// Set some data in old format

}
