package e2e

import (
	"reflect"

	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"
	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
	tmproto "github.com/tendermint/tendermint/proto/tendermint/types"
)

// TestProviderKeeperFields tests that the provider keeper is initialized with non-zero and
// non-nil values for all its fields. This is a direct test of the provider app initer given to the test suite.
func (s CCVTestSuite) TestProviderKeeperFields() {

	providerKeeper := s.providerApp.GetProviderKeeper()

	cdc, storeKey, paramSpace, scopedKeeper, channelKeeper, portKeeper, connectionKeeper,
		accountKeeper, clientKeeper, stakingKeeper, slashingKeeper, evidenceKeeper,
		feeColl := providerKeeper.ExposeAllFields()

	s.Require().False(reflect.ValueOf(cdc).IsZero())              // 1
	s.Require().False(reflect.ValueOf(storeKey).IsZero())         // 2
	s.Require().False(reflect.ValueOf(paramSpace).IsZero())       // 3
	s.Require().False(reflect.ValueOf(scopedKeeper).IsZero())     // 4
	s.Require().False(reflect.ValueOf(channelKeeper).IsZero())    // 5
	s.Require().False(reflect.ValueOf(portKeeper).IsZero())       // 6
	s.Require().False(reflect.ValueOf(connectionKeeper).IsZero()) // 7
	s.Require().False(reflect.ValueOf(accountKeeper).IsZero())    // 8
	s.Require().False(reflect.ValueOf(clientKeeper).IsZero())     // 9
	s.Require().False(reflect.ValueOf(stakingKeeper).IsZero())    // 10
	s.Require().False(reflect.ValueOf(slashingKeeper).IsZero())   // 11
	s.Require().False(reflect.ValueOf(evidenceKeeper).IsZero())   // 12
	s.Require().False(reflect.ValueOf(feeColl).IsZero())          // 13

	// Ensures we didn't miss any fields
	s.Require().Equal(13, reflect.ValueOf(providerKeeper).NumField())
}

// TestConsumerKeeperFields tests that the consumer keeper is initialized with non-zero and
// non-nil values for all its fields. This is a direct test of the consumer app initer given to the test suite.
func (s CCVTestSuite) TestConsumerKeeperFields() {
	consumerKeeper := s.consumerApp.GetConsumerKeeper()

	storeKey, cdc, paramSpace, scopedKeeper, channelKeeper, portKeeper, connectionKeeper,
		clientKeeper, slashingKeeper, hooks, bankKeeper, accountKeeper, ibcTransferKeeper,
		ibcCoreKeeper, feeColl := consumerKeeper.ExposeAllFields()

	s.Require().False(reflect.ValueOf(storeKey).IsZero())          // 1
	s.Require().False(reflect.ValueOf(cdc).IsZero())               // 2
	s.Require().False(reflect.ValueOf(paramSpace).IsZero())        // 3
	s.Require().False(reflect.ValueOf(scopedKeeper).IsZero())      // 4
	s.Require().False(reflect.ValueOf(channelKeeper).IsZero())     // 5
	s.Require().False(reflect.ValueOf(portKeeper).IsZero())        // 6
	s.Require().False(reflect.ValueOf(connectionKeeper).IsZero())  // 7
	s.Require().False(reflect.ValueOf(clientKeeper).IsZero())      // 8
	s.Require().False(reflect.ValueOf(slashingKeeper).IsZero())    // 9
	s.Require().False(reflect.ValueOf(hooks).IsZero())             // 10
	s.Require().False(reflect.ValueOf(bankKeeper).IsZero())        // 11
	s.Require().False(reflect.ValueOf(accountKeeper).IsZero())     // 12
	s.Require().False(reflect.ValueOf(ibcTransferKeeper).IsZero()) // 13
	s.Require().False(reflect.ValueOf(ibcCoreKeeper).IsZero())     // 14
	s.Require().False(reflect.ValueOf(feeColl).IsZero())           // 15

	// Ensures we didn't miss any fields
	s.Require().Equal(15, reflect.ValueOf(consumerKeeper).NumField())
}

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
