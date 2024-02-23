package integration

import (
	"github.com/cosmos/ibc-go/v7/testing/mock"

	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	tmencoding "github.com/cometbft/cometbft/crypto/encoding"
	tmprotocrypto "github.com/cometbft/cometbft/proto/tendermint/crypto"

	providerkeeper "github.com/cosmos/interchain-security/v4/x/ccv/provider/keeper"
	ccv "github.com/cosmos/interchain-security/v4/x/ccv/types"
)

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
				err := pk.AssignConsumerKey(s.providerCtx(), s.consumerChain.ChainID, validator, consumerKey)
				if err != nil {
					return err
				}

				// check that a VSCPacket is queued
				nextBlocks(s.providerChain, providerkeeper.BlocksPerEpoch)
				//s.providerChain.NextBlock()
				pendingPackets := pk.GetPendingVSCPackets(s.providerCtx(), s.consumerChain.ChainID)
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
				err := pk.AssignConsumerKey(s.providerCtx(), s.consumerChain.ChainID, validator, consumerKey)
				if err != nil {
					return err
				}
				nextBlocks(s.providerChain, providerkeeper.BlocksPerEpoch)
				//
				//s.providerChain.NextBlock()

				return nil
			}, false, 2,
		},
		{
			"assignment with power change", func(pk *providerkeeper.Keeper) error {
				// establish CCV channel
				s.SetupCCVChannel(s.path)

				// key assignment
				validator, consumerKey := generateNewConsumerKey(s, 0)
				err := pk.AssignConsumerKey(s.providerCtx(), s.consumerChain.ChainID, validator, consumerKey)
				if err != nil {
					return err
				}

				// Bond some tokens on provider to change validator powers
				bondAmt := sdk.NewInt(1000000)
				delAddr := s.providerChain.SenderAccount.GetAddress()
				delegate(s, delAddr, bondAmt)

				//s.providerChain.NextBlock()
				nextBlocks(s.providerChain, providerkeeper.BlocksPerEpoch)

				return nil
			}, false, 2,
		},
		{
			"double same-key assignment in same block", func(pk *providerkeeper.Keeper) error {
				// establish CCV channel
				s.SetupCCVChannel(s.path)

				// key assignment
				validator, consumerKey := generateNewConsumerKey(s, 0)
				err := pk.AssignConsumerKey(s.providerCtx(), s.consumerChain.ChainID, validator, consumerKey)
				if err != nil {
					return err
				}

				// same key assignment
				err = pk.AssignConsumerKey(s.providerCtx(), s.consumerChain.ChainID, validator, consumerKey)
				if err != nil {
					return err
				}
				//s.providerChain.NextBlock()
				nextBlocks(s.providerChain, providerkeeper.BlocksPerEpoch)

				return nil
			}, true, 2,
		},
		{
			"double key assignment in same block", func(pk *providerkeeper.Keeper) error {
				// establish CCV channel
				s.SetupCCVChannel(s.path)

				// key assignment
				validator, consumerKey := generateNewConsumerKey(s, 0)
				err := pk.AssignConsumerKey(s.providerCtx(), s.consumerChain.ChainID, validator, consumerKey)
				if err != nil {
					return err
				}

				// same key assignment
				validator, consumerKey = generateNewConsumerKey(s, 0)
				err = pk.AssignConsumerKey(s.providerCtx(), s.consumerChain.ChainID, validator, consumerKey)
				if err != nil {
					return err
				}
				//s.providerChain.NextBlock()
				nextBlocks(s.providerChain, providerkeeper.BlocksPerEpoch)

				return nil
			}, false, 2,
		},
		{
			"double same-key assignment in different blocks", func(pk *providerkeeper.Keeper) error {
				// establish CCV channel
				s.SetupCCVChannel(s.path)

				// key assignment
				validator, consumerKey := generateNewConsumerKey(s, 0)
				err := pk.AssignConsumerKey(s.providerCtx(), s.consumerChain.ChainID, validator, consumerKey)
				if err != nil {
					return err
				}
				nextBlocks(s.providerChain, providerkeeper.BlocksPerEpoch)
				//s.providerChain.NextBlock()

				// same key assignment
				err = pk.AssignConsumerKey(s.providerCtx(), s.consumerChain.ChainID, validator, consumerKey)
				if err != nil {
					return err
				}
				//s.providerChain.NextBlock()
				nextBlocks(s.providerChain, providerkeeper.BlocksPerEpoch)

				return nil
			}, true, 2,
		},
		{
			"double key assignment in different blocks", func(pk *providerkeeper.Keeper) error {
				// establish CCV channel
				s.SetupCCVChannel(s.path)

				// key assignment
				validator, consumerKey := generateNewConsumerKey(s, 0)
				err := pk.AssignConsumerKey(s.providerCtx(), s.consumerChain.ChainID, validator, consumerKey)
				if err != nil {
					return err
				}
				//s.providerChain.NextBlock()
				nextBlocks(s.providerChain, providerkeeper.BlocksPerEpoch)

				// same key assignment
				validator, consumerKey = generateNewConsumerKey(s, 0)
				err = pk.AssignConsumerKey(s.providerCtx(), s.consumerChain.ChainID, validator, consumerKey)
				if err != nil {
					return err
				}
				//s.providerChain.NextBlock()
				nextBlocks(s.providerChain, providerkeeper.BlocksPerEpoch)

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
			bondAmt := sdk.NewInt(1000000)
			delAddr := s.providerChain.SenderAccount.GetAddress()
			delegate(s, delAddr, bondAmt)

			// Send CCV packet to consumer
			s.providerChain.NextBlock()

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
