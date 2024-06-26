package integration

import (
	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"

	tmproto "github.com/cometbft/cometbft/proto/tendermint/types"

	consumertypes "github.com/cosmos/interchain-security/v5/x/ccv/consumer/types"
	ccvtypes "github.com/cosmos/interchain-security/v5/x/ccv/types"
)

// Tests the tracking of historical info in the context of new blocks being committed
func (k CCVTestSuite) TestHistoricalInfo() { //nolint:govet // this is a test so we can copy locks
	consumerKeeper := k.consumerApp.GetConsumerKeeper()
	cCtx := k.consumerChain.GetContext

	// save init consumer valset length
	initValsetLen := len(consumerKeeper.GetAllCCValidator(cCtx()))
	// save current block height
	initHeight := cCtx().BlockHeight()

	// define an utility function that creates a new cross-chain validator
	// and then call track historical info in the next block
	createVal := func(k CCVTestSuite) { //nolint:govet // this is a test so we can copy locks
		// add new validator to consumer states
		pk := ed25519.GenPrivKey().PubKey()
		cVal, err := consumertypes.NewCCValidator(pk.Address(), int64(1), pk)
		k.Require().NoError(err)

		consumerKeeper.SetCCValidator(k.consumerChain.GetContext(), cVal)

		// commit block in order to call TrackHistoricalInfo
		k.consumerChain.NextBlock()
	}

	// testsetup create 2 validators and then call track historical info with header block height
	// increased by HistoricalEntries in order to prune the historical info less or equal to the current block height
	// Note that historical info containing the created validators were stored during the BeginBlocker of the current block
	// at the moment of creation and thus are indexed with the respective block heights InitHeight and InitHeight+1
	// Last saved historical info was in the last commited block k.consumerChain.GetContext().BlockHeight(), meaning that
	// if we want to prune old entries we need to start from the last saved historical info which is k.consumerChain.GetContext().BlockHeight() - 1
	testSetup := []func(CCVTestSuite){
		createVal,
		createVal,
		func(k CCVTestSuite) { //nolint:govet // this is a test so we can copy locks
			historicalEntries := k.consumerApp.GetConsumerKeeper().GetHistoricalEntries(k.consumerCtx())
			newHeight := k.consumerChain.GetContext().BlockHeight() - 1 + historicalEntries
			header := tmproto.Header{
				ChainID: "HelloChain",
				Height:  newHeight,
			}
			ctx := k.consumerChain.GetContext().WithBlockHeader(header)
			consumerKeeper.TrackHistoricalInfo(ctx)
		},
	}

	for _, ts := range testSetup {
		ts(k) //nolint:govet // this is a test so we can copy locks
	}

	// test cases verify that historical info entries are pruned when their height
	// is below CurrentHeight - HistoricalEntries, and check that their valset gets updated
	testCases := []struct {
		height       int64
		expectsError bool
		expLen       int
	}{
		{
			height:       initHeight,
			expectsError: true,
			expLen:       0,
		},
		{
			height:       initHeight + 1,
			expectsError: true,
			expLen:       0,
		},
		{
			height:       initHeight + ccvtypes.DefaultHistoricalEntries + 1,
			expectsError: false,
			expLen:       initValsetLen + 2,
		},
	}

	for _, tc := range testCases {
		cCtx().WithBlockHeight(tc.height)
		hi, err := consumerKeeper.GetHistoricalInfo(cCtx().WithBlockHeight(tc.height), tc.height)
		k.Require().Equal(tc.expectsError, err != nil)
		k.Require().Len(hi.Valset, tc.expLen)
	}
}
