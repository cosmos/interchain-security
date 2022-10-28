package provider_test

import (
	"strings"
	"testing"

	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"
	tmproto "github.com/tendermint/tendermint/proto/tendermint/types"

	"github.com/cosmos/cosmos-sdk/testutil/testdata"
	sdk "github.com/cosmos/cosmos-sdk/types"
	testkeeper "github.com/cosmos/interchain-security/testutil/keeper"
	"github.com/cosmos/interchain-security/x/ccv/provider"
	"github.com/cosmos/interchain-security/x/ccv/provider/keeper"
)

type Helper struct {
	t       *testing.T
	keeper  keeper.Keeper
	ctx     sdk.Context
	ctrl    *gomock.Controller
	mocks   testkeeper.MockedKeepers
	handler sdk.Handler
}

func MakeHelper(t *testing.T) Helper {
	k, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()
	return Helper{
		t,
		k,
		ctx,
		ctrl,
		mocks,
		provider.NewHandler(k),
	}
}

func TestInvalidMsg(t *testing.T) {
	h := MakeHelper(t)
	res, err := h.handler(sdk.NewContext(nil, tmproto.Header{}, false, nil), testdata.NewTestMsg())
	require.Error(t, err)
	require.Nil(t, res)
	require.True(t, strings.Contains(err.Error(), "unrecognized provider message type"))
}

func TestDesignateConsensusKeyForConsumerChainHappy(t *testing.T) {
	h := MakeHelper(t)

}
