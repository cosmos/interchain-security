package integration

import (
	tmproto "github.com/cometbft/cometbft/proto/tendermint/types"
	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"
	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
)

// Tests the tracking of historical info in the context of new blocks being committed
func (s CCVTestSuite) TestHistoricalInfo() {
	consumerKeeper := s.consumerApp.GetConsumerKeeper()
	cCtx := s.consumerChain.GetContext

	// save init consumer valset length
	initValsetLen := len(consumerKeeper.GetAllCCValidator(cCtx()))
	// save current block height
	initHeight := cCtx().BlockHeight()

	// define an utility function that creates a new cross-chain validator
	// and then call track historical info in the next block
	createVal := func(s CCVTestSuite) {
		// add new validator to consumer states
		pk := ed25519.GenPrivKey().PubKey()
		cVal, err := consumertypes.NewCCValidator(pk.Address(), int64(1), pk)
		s.Require().NoError(err)

		consumerKeeper.SetCCValidator(s.consumerChain.GetContext(), cVal)

		// commit block in order to call TrackHistoricalInfo
		s.consumerChain.NextBlock()
	}

	// testsetup create 2 validators and then call track historical info with header block height
	// increased by HistoricalEntries in order to prune the historical info less or equal to the current block height
	// Note that historical info containing the created validators are stored during the next block BeginBlocker
	// and thus are indexed with the respective block heights InitHeight+1 and InitHeight+2
	testSetup := []func(CCVTestSuite){
		createVal,
		createVal,
		func(s CCVTestSuite) {
			historicalEntries := s.consumerApp.GetConsumerKeeper().GetHistoricalEntries(s.consumerCtx())
			newHeight := s.consumerChain.GetContext().BlockHeight() + historicalEntries
			header := tmproto.Header{
				ChainID: "HelloChain",
				Height:  newHeight,
			}
			ctx := s.consumerChain.GetContext().WithBlockHeader(header)
			consumerKeeper.TrackHistoricalInfo(ctx)
		},
	}

	for _, ts := range testSetup {
		ts(s) 
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
			height: initHeight + consumertypes.DefaultHistoricalEntries + 2,
			found:  true,
			expLen: initValsetLen + 2,
		},
	}

	for _, tc := range testCases {
		cCtx().WithBlockHeight(tc.height)
		hi, found := consumerKeeper.GetHistoricalInfo(cCtx().WithBlockHeight(tc.height), tc.height)
		s.Require().Equal(tc.found, found)
		s.Require().Len(hi.Valset, tc.expLen)
	}
}
