package integration

import (
	"github.com/cosmos/ibc-go/v9/testing/mock"

	"cosmossdk.io/math"

	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	tmencoding "github.com/cometbft/cometbft/crypto/encoding"
	tmprotocrypto "github.com/cometbft/cometbft/proto/tendermint/crypto"

	providerkeeper "github.com/cosmos/interchain-security/v7/x/ccv/provider/keeper"
	"github.com/cosmos/interchain-security/v7/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/v7/x/ccv/types"
)

// TestKeyAssignment tests key assignments relayed from the provider chain to the consumer chain at different times in the protocol lifecycle.
// @Long Description@
// Each test scenario sets up a provider chain and then assigns a key for a validator.
// However, the assignment comes at different times in the protocol lifecycle.
// The test covers the following scenarios:
// * successfully assign the key before the CCV channel initialization is complete, then check that a VSCPacket is indeed queued
// * successfully assign the key after the CCV channel initialization is complete
// * successfully assign the key during an same epoch where the validator power changes
// * get an error when assigning the same key twice in the same block by different validators
// * get an error when assigning the same key twice in the same block by the same validator
// * successfully assign two different keys in the same block by one validator
// * get an error when assigning the same key twice in different blocks by different validators
// * get an error when assigning the same key twice in different blocks by the same validator
// For each scenario where the key assignment does not produce an error,
// the test also checks that VSCPackets are relayed to the consumer chain and that the clients on
// the provider and consumer chain can be updated.
// TODO: Remove panics when unexpected error occurs.
func (s *CCVTestSuite) TestKeyAssignment() {
	testCases := []struct {
		name           string
		assignFunc     func(*providerkeeper.Keeper) error
		expError       bool
		expPacketCount int
	}{
		{
			"assignment during channel init", func(pk *providerkeeper.Keeper) error {
				// key assignment
				validator, consumerKey := generateNewConsumerKey(s, 0)
				err := pk.AssignConsumerKey(s.providerCtx(), s.getFirstBundle().ConsumerId, validator, consumerKey)
				if err != nil {
					return err
				}

				// check that a VSCPacket is queued
				s.nextEpoch()
				pendingPackets := pk.GetPendingVSCPackets(s.providerCtx(), s.getFirstBundle().ConsumerId)
				s.Require().Len(pendingPackets, 1)

				// establish CCV channel
				s.SetupCCVChannel(s.path)

				return nil
			}, false, 2,
		},
		{
			"assignment after channel init", func(pk *providerkeeper.Keeper) error {
				// establish CCV channel
				s.SetupCCVChannel(s.path)

				// key assignment
				validator, consumerKey := generateNewConsumerKey(s, 0)
				err := pk.AssignConsumerKey(s.providerCtx(), s.getFirstBundle().ConsumerId, validator, consumerKey)
				if err != nil {
					return err
				}

				s.nextEpoch()

				return nil
			}, false, 2,
		},
		{
			"assignment with power change", func(pk *providerkeeper.Keeper) error {
				// establish CCV channel
				s.SetupCCVChannel(s.path)

				// key assignment
				validator, consumerKey := generateNewConsumerKey(s, 0)
				err := pk.AssignConsumerKey(s.providerCtx(), s.getFirstBundle().ConsumerId, validator, consumerKey)
				if err != nil {
					return err
				}

				// Bond some tokens on provider to change validator powers
				bondAmt := math.NewInt(1000000)
				delAddr := s.providerChain.SenderAccount.GetAddress()
				delegate(s, delAddr, bondAmt)

				s.nextEpoch()

				return nil
			}, false, 2,
		},
		{
			"double same-key assignment in same block by different vals", func(pk *providerkeeper.Keeper) error {
				// establish CCV channel
				s.SetupCCVChannel(s.path)

				// key assignment
				validator, consumerKey := generateNewConsumerKey(s, 0)
				err := pk.AssignConsumerKey(s.providerCtx(), s.getFirstBundle().ConsumerId, validator, consumerKey)
				if err != nil {
					panic(err)
				}

				// same key assignment, but different validator
				validator2, _ := generateNewConsumerKey(s, 1)
				err = pk.AssignConsumerKey(s.providerCtx(), s.getFirstBundle().ConsumerId, validator2, consumerKey)
				if err != nil {
					return err
				}
				s.nextEpoch()

				return nil
			}, true, 2,
		},
		{
			"double same-key assignment in same block by same val", func(pk *providerkeeper.Keeper) error {
				// establish CCV channel
				s.SetupCCVChannel(s.path)

				// key assignment
				validator, consumerKey := generateNewConsumerKey(s, 0)
				err := pk.AssignConsumerKey(s.providerCtx(), s.getFirstBundle().ConsumerId, validator, consumerKey)
				if err != nil {
					panic(err)
				}

				// same key assignment, but different validator
				err = pk.AssignConsumerKey(s.providerCtx(), s.getFirstBundle().ConsumerId, validator, consumerKey)
				if err != nil {
					return err
				}
				s.nextEpoch()

				return nil
			}, true, 2,
		},
		{
			"double key assignment in same block by same val", func(pk *providerkeeper.Keeper) error {
				// establish CCV channel
				s.SetupCCVChannel(s.path)

				// key assignment
				validator, consumerKey := generateNewConsumerKey(s, 0)
				err := pk.AssignConsumerKey(s.providerCtx(), s.getFirstBundle().ConsumerId, validator, consumerKey)
				if err != nil {
					return err
				}

				// same key assignment
				validator, consumerKey = generateNewConsumerKey(s, 0)
				err = pk.AssignConsumerKey(s.providerCtx(), s.getFirstBundle().ConsumerId, validator, consumerKey)
				if err != nil {
					return err
				}

				s.nextEpoch()

				return nil
			}, false, 2,
		},
		{
			"double same-key assignment in different blocks by different vals", func(pk *providerkeeper.Keeper) error {
				// establish CCV channel
				s.SetupCCVChannel(s.path)

				// key assignment
				validator, consumerKey := generateNewConsumerKey(s, 0)
				err := pk.AssignConsumerKey(s.providerCtx(), s.getFirstBundle().ConsumerId, validator, consumerKey)
				if err != nil {
					panic(err)
				}

				s.nextEpoch()

				// same key assignment
				validator2, _ := generateNewConsumerKey(s, 1)
				err = pk.AssignConsumerKey(s.providerCtx(), s.getFirstBundle().ConsumerId, validator2, consumerKey)
				if err != nil {
					return err
				}

				// check that the key was not assigned to the second validator
				valConsAddr2, getConsAddrErr := validator2.GetConsAddr() // make sure we don't override err, which we are saving for below
				s.Require().NoError(getConsAddrErr)
				actualConsumerKey2, found := pk.GetValidatorConsumerPubKey(s.providerCtx(), s.consumerChain.ChainID, types.NewProviderConsAddress(valConsAddr2))
				s.Require().True(found)
				// the key for the second validator should *not* be the one we just assigned to the first validator
				s.Require().NotEqual(consumerKey, actualConsumerKey2)

				s.nextEpoch()

				return nil
			}, true, 2,
		},
		{
			"double same-key assignment in different blocks by same val", func(pk *providerkeeper.Keeper) error {
				// establish CCV channel
				s.SetupCCVChannel(s.path)

				// key assignment
				validator, consumerKey := generateNewConsumerKey(s, 0)
				err := pk.AssignConsumerKey(s.providerCtx(), s.getFirstBundle().ConsumerId, validator, consumerKey)
				if err != nil {
					return err
				}

				s.nextEpoch()

				// same key assignment
				err = pk.AssignConsumerKey(s.providerCtx(), s.getFirstBundle().ConsumerId, validator, consumerKey)
				if err != nil {
					return err
				}
				s.nextEpoch()

				return nil
			}, true, 2,
		},
		{
			"double key assignment in different blocks by same val", func(pk *providerkeeper.Keeper) error {
				// establish CCV channel
				s.SetupCCVChannel(s.path)

				// key assignment
				validator, consumerKey := generateNewConsumerKey(s, 0)
				err := pk.AssignConsumerKey(s.providerCtx(), s.getFirstBundle().ConsumerId, validator, consumerKey)
				if err != nil {
					return err
				}

				s.nextEpoch()

				// same key assignment
				validator, consumerKey = generateNewConsumerKey(s, 0)
				err = pk.AssignConsumerKey(s.providerCtx(), s.getFirstBundle().ConsumerId, validator, consumerKey)
				if err != nil {
					return err
				}

				s.nextEpoch()

				return nil
			}, false, 3,
		},
		// TODO: this test should pass if we manage to change the client update mode to sequential
		// {
		// 	"key assignment for all validators in the same block", func(pk *providerkeeper.Keeper) error {
		// 		// establish CCV channel
		// 		s.SetupCCVChannel(s.path)

		// 		// key assignment
		// 		for i, _ := range s.providerChain.Vals.Validators {
		// 			validator, consumerKey := generateNewConsumerKey(s, i)
		// 			err := pk.AssignConsumerKey(s.providerCtx(), s.consumerChain.ChainID, validator, consumerKey)
		// 			if err != nil {
		// 				return err
		// 			}
		// 		}
		// 		// vscPakcketData := pk.GetPendingPackets(s.providerCtx(), s.consumerChain.ChainID)
		// 		// s.Require().Len(vscPakcketData, 1)
		// 		// s.Require().Len(vscPakcketData[0].ValidatorUpdates, 2*len(s.providerChain.Vals.Validators))

		// 		s.providerChain.NextBlock()

		// 		return nil
		// 	}, false, 2,
		// },
	}
	for i, tc := range testCases {
		providerKeeper := s.providerApp.GetProviderKeeper()

		err := tc.assignFunc(&providerKeeper)
		if tc.expError {
			s.Require().Error(err, "test: "+tc.name)
		} else {
			s.Require().NoError(err, "test: "+tc.name)
		}

		if !tc.expError {
			// Bond some tokens on provider to change validator powers
			bondAmt := math.NewInt(1000000)
			delAddr := s.providerChain.SenderAccount.GetAddress()
			delegate(s, delAddr, bondAmt)

			// Send CCV packet to consumer
			// s.providerChain.NextBlock()
			s.nextEpoch()

			// Relay all VSC packets from provider to consumer
			relayAllCommittedPackets(
				s,
				s.providerChain,
				s.path,
				ccv.ProviderPortID,
				s.path.EndpointB.ChannelID,
				tc.expPacketCount,
				"test: "+tc.name,
			)

			// update clients
			err := s.path.EndpointA.UpdateClient()
			s.Require().NoError(err)
			err = s.path.EndpointB.UpdateClient()
			s.Require().NoError(err)
		}

		if i+1 < len(testCases) {
			// reset suite to reset provider client
			s.SetupTest()
		}
	}
}

// generateNewConsumerKey generate new consumer key for the validator with valIndex
func generateNewConsumerKey(s *CCVTestSuite, valIndex int) (stakingtypes.Validator, tmprotocrypto.PublicKey) {
	// get validator
	s.Require().Less(valIndex, len(s.providerChain.Vals.Validators))
	_, valAddr := s.getValByIdx(valIndex)
	validator := s.getVal(s.providerCtx(), valAddr)

	// generate new PrivValidator
	privVal := mock.NewPV()
	tmPubKey, err := privVal.GetPubKey()
	s.Require().NoError(err)
	pubKey, err := tmencoding.PubKeyToProto(tmPubKey)
	s.Require().NoError(err)

	// add Signer to the consumer chain
	s.consumerChain.Signers[tmPubKey.Address().String()] = privVal

	return validator, pubKey
}
