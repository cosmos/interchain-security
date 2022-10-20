package e2e

import (
	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"
	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
	tmproto "github.com/tendermint/tendermint/proto/tendermint/types"
)

// Tests the tracking of historical info in the context of new blocks being committed
func (k CCVTestSuite) TestHistoricalInfo() {
	consumerKeeper := k.consumerApp.GetConsumerKeeper()
	cCtx := k.consumerChain.GetContext

	// save init consumer valset length
	initValsetLen := len(consumerKeeper.GetAllCCValidator(cCtx()))
	// save current block height
	initHeight := cCtx().BlockHeight()

	// define an utility function that creates a new cross-chain validator
	// and then call track historical info in the next block
	createVal := func(k CCVTestSuite) {
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
	// Note that historical info containing the created validators are stored during the next block BeginBlocker
	// and thus are indexed with the respective block heights InitHeight+1 and InitHeight+2
	testSetup := []func(CCVTestSuite){
		createVal,
		createVal,
		func(k CCVTestSuite) {
			historicalEntries := k.consumerApp.GetConsumerKeeper().GetHistoricalEntries(k.consumerCtx())
			newHeight := k.consumerChain.GetContext().BlockHeight() + historicalEntries
			header := tmproto.Header{
				ChainID: "HelloChain",
				Height:  newHeight,
			}
			ctx := k.consumerChain.GetContext().WithBlockHeader(header)
			consumerKeeper.TrackHistoricalInfo(ctx)
		},
	}

	for _, ts := range testSetup {
		ts(k)
	}

	// test cases verify that historical info entries are pruned when their height
	// is below CurrentHeight - HistoricalEntries, and check that their valset gets updated
	testCases := []struct {
		height int64
		found  bool
		expLen int
	}{
		{
			height: initHeight + 1,
			found:  false,
			expLen: 0,
		},
		{
			height: initHeight + 2,
			found:  false,
			expLen: 0,
		},
		{
			height: initHeight + int64(consumertypes.DefaultHistoricalEntries) + 2,
			found:  true,
			expLen: initValsetLen + 2,
		},
	}

	for _, tc := range testCases {
		cCtx().WithBlockHeight(tc.height)
		hi, found := consumerKeeper.GetHistoricalInfo(cCtx().WithBlockHeight(tc.height), tc.height)
		k.Require().Equal(tc.found, found)
		k.Require().Len(hi.Valset, tc.expLen)
	}
}
