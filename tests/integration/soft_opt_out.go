package integration

import (
	"bytes"
	"sort"

	abci "github.com/cometbft/cometbft/abci/types"
	sdk "github.com/cosmos/cosmos-sdk/types"
	slashingkeeper "github.com/cosmos/cosmos-sdk/x/slashing/keeper"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	consumerKeeper "github.com/cosmos/interchain-security/v3/x/ccv/consumer/keeper"
	ccv "github.com/cosmos/interchain-security/v3/x/ccv/types"
)

// TestSoftOptOut tests the soft opt-out feature
//   - if a validator in the top 95% doesn't sign 50 blocks on the consumer, a SlashPacket is sent to the provider
//   - if a validator in the bottom 5% doesn't sign 50 blocks on the consumer, a SlashPacket is NOT sent to the provider
//   - if a validator in the bottom 5% doesn't sign 49 blocks on the consumer,
//     then it moves to the top 95% and doesn't sign one more block, a SlashPacket is NOT sent to the provider
func (suite *CCVTestSuite) TestSoftOptOut() {
	var votes []abci.VoteInfo

	testCases := []struct {
		name            string
		downtimeFunc    func(*consumerKeeper.Keeper, *slashingkeeper.Keeper, []byte, int)
		targetValidator int
		expJailed       bool
		expSlashPacket  bool
	}{
		{
			"downtime top 95%",
			func(ck *consumerKeeper.Keeper, sk *slashingkeeper.Keeper, valAddr []byte, valIdx int) {
				for i, voteInfo := range votes {
					if bytes.Equal(voteInfo.Validator.Address, valAddr) {
						votes[i].SignedLastBlock = false
					}
				}
				blocksToDowntime := sk.SignedBlocksWindow(suite.consumerCtx()) - sk.MinSignedPerWindow(suite.consumerCtx()) + 1
				slashingBeginBlocker(suite, votes, blocksToDowntime)
			},
			0,
			true,
			true,
		},
		{
			"downtime bottom 5%",
			func(ck *consumerKeeper.Keeper, sk *slashingkeeper.Keeper, valAddr []byte, valIdx int) {
				for i, voteInfo := range votes {
					if bytes.Equal(voteInfo.Validator.Address, valAddr) {
						votes[i].SignedLastBlock = false
					}
				}
				blocksToDowntime := sk.SignedBlocksWindow(suite.consumerCtx()) - sk.MinSignedPerWindow(suite.consumerCtx()) + 1
				slashingBeginBlocker(suite, votes, blocksToDowntime)
			},
			3,
			true,
			false,
		},
		{
			"downtime bottom 5% first and then top 95%, but not enough",
			func(ck *consumerKeeper.Keeper, sk *slashingkeeper.Keeper, valAddr []byte, valIdx int) {
				for i, voteInfo := range votes {
					if bytes.Equal(voteInfo.Validator.Address, valAddr) {
						votes[i].SignedLastBlock = false
					}
				}
				blocksToDowntime := sk.SignedBlocksWindow(suite.consumerCtx()) - sk.MinSignedPerWindow(suite.consumerCtx())
				slashingBeginBlocker(suite, votes, blocksToDowntime)

				// Increase the power of this validator (to bring it in the top 95%)
				delAddr := suite.providerChain.SenderAccount.GetAddress()
				bondAmt := sdk.NewInt(100).Mul(sdk.DefaultPowerReduction)
				delegateByIdx(suite, delAddr, bondAmt, valIdx)

				suite.providerChain.NextBlock()

				// Relay 1 VSC packet from provider to consumer
				relayAllCommittedPackets(suite, suite.providerChain, suite.path, ccv.ProviderPortID, suite.path.EndpointB.ChannelID, 1)

				// Update validator from store
				val, found := ck.GetCCValidator(suite.consumerCtx(), valAddr)
				suite.Require().True(found)
				smallestNonOptOutPower := ck.GetSmallestNonOptOutPower(suite.consumerCtx())
				suite.Require().Equal(val.Power, smallestNonOptOutPower)

				// Let the validator continue not signing, but not enough to get jailed
				for i, voteInfo := range votes {
					if bytes.Equal(voteInfo.Validator.Address, valAddr) {
						votes[i].Validator.Power = val.Power
					}
				}
				slashingBeginBlocker(suite, votes, 10)
			},
			2,
			false,
			false,
		},
		{
			"donwtime bottom 5% first and then top 95% until jailed",
			func(ck *consumerKeeper.Keeper, sk *slashingkeeper.Keeper, valAddr []byte, valIdx int) {
				for i, voteInfo := range votes {
					if bytes.Equal(voteInfo.Validator.Address, valAddr) {
						votes[i].SignedLastBlock = false
					}
				}
				blocksToDowntime := sk.SignedBlocksWindow(suite.consumerCtx()) - sk.MinSignedPerWindow(suite.consumerCtx())
				slashingBeginBlocker(suite, votes, blocksToDowntime)

				// Increase the power of this validator (to bring it in the top 95%)
				delAddr := suite.providerChain.SenderAccount.GetAddress()
				bondAmt := sdk.NewInt(100).Mul(sdk.DefaultPowerReduction)
				delegateByIdx(suite, delAddr, bondAmt, valIdx)

				suite.providerChain.NextBlock()

				// Relay 1 VSC packet from provider to consumer
				relayAllCommittedPackets(suite, suite.providerChain, suite.path, ccv.ProviderPortID, suite.path.EndpointB.ChannelID, 1)

				// Update validator from store
				val, found := ck.GetCCValidator(suite.consumerCtx(), valAddr)
				suite.Require().True(found)
				smallestNonOptOutPower := ck.GetSmallestNonOptOutPower(suite.consumerCtx())
				suite.Require().Equal(val.Power, smallestNonOptOutPower)

				// Let the validator continue not signing until it gets jailed.
				// Due to the starting height being just updated, the signed blocked window needs to pass.
				for i, voteInfo := range votes {
					if bytes.Equal(voteInfo.Validator.Address, valAddr) {
						votes[i].Validator.Power = val.Power
					}
				}
				slashingBeginBlocker(suite, votes, sk.SignedBlocksWindow(suite.consumerCtx())+1)
			},
			2,
			true,
			true,
		},
	}

	for i, tc := range testCases {
		// initial setup
		suite.SetupCCVChannel(suite.path)

		consumerKeeper := suite.consumerApp.GetConsumerKeeper()
		consumerSlashingKeeper := suite.consumerApp.GetTestSlashingKeeper()

		// Setup validator power s.t. the bottom 5% is non-empty
		validatorPowers := []int64{1000, 500, 50, 10}
		suite.setupValidatorPowers(validatorPowers)

		// Relay 1 VSC packet from provider to consumer
		relayAllCommittedPackets(suite, suite.providerChain, suite.path, ccv.ProviderPortID, suite.path.EndpointB.ChannelID, 1)

		// Check that the third validator is the first in the top 95%
		smallestNonOptOutPower := consumerKeeper.GetSmallestNonOptOutPower(suite.consumerCtx())
		suite.Require().Equal(validatorPowers[1], smallestNonOptOutPower, "test: "+tc.name)

		// Get the list of all CCV validators
		vals := consumerKeeper.GetAllCCValidator(suite.consumerCtx())
		// Note that GetAllCCValidator is iterating over a map so the result need to be sorted
		sort.Slice(vals, func(i, j int) bool {
			if vals[i].Power != vals[j].Power {
				return vals[i].Power > vals[j].Power
			}
			return bytes.Compare(vals[i].Address, vals[j].Address) > 0
		})

		// Let everyone sign the first 100 blocks (default value for slahing.SignedBlocksWindow param).
		// This populates the signingInfo of the slashing module so that
		// the check for starting height passes.
		votes = []abci.VoteInfo{}
		for _, val := range vals {
			votes = append(votes, abci.VoteInfo{
				Validator:       abci.Validator{Address: val.Address, Power: val.Power},
				SignedLastBlock: true,
			})
		}
		slashingBeginBlocker(suite, votes, consumerSlashingKeeper.SignedBlocksWindow(suite.consumerCtx()))

		// Downtime infraction
		sk := consumerSlashingKeeper.(slashingkeeper.Keeper)
		tc.downtimeFunc(&consumerKeeper, &sk, vals[tc.targetValidator].Address, tc.targetValidator)

		// Check the signing info for target validator
		consAddr := sdk.ConsAddress(vals[tc.targetValidator].Address)
		info, _ := consumerSlashingKeeper.GetValidatorSigningInfo(suite.consumerCtx(), consAddr)
		if tc.expJailed {
			// expect increased jail time
			suite.Require().True(
				info.JailedUntil.Equal(suite.consumerCtx().BlockTime().Add(consumerSlashingKeeper.DowntimeJailDuration(suite.consumerCtx()))),
				"test: "+tc.name+"; did not update validator jailed until signing info",
			)
			// expect missed block counters reset
			suite.Require().Zero(info.MissedBlocksCounter, "test: "+tc.name+"; did not reset validator missed block counter")
			suite.Require().Zero(info.IndexOffset, "test: "+tc.name)
			consumerSlashingKeeper.IterateValidatorMissedBlockBitArray(suite.consumerCtx(), consAddr, func(_ int64, missed bool) bool {
				suite.Require().True(missed, "test: "+tc.name)
				return false
			})
		} else {
			suite.Require().True(
				// expect not increased jail time
				info.JailedUntil.Before(suite.consumerCtx().BlockTime()),
				"test: "+tc.name+"; validator jailed until signing info was updated",
			)
			suite.Require().Positive(info.IndexOffset, "test: "+tc.name)
		}

		pendingPackets := consumerKeeper.GetPendingPackets(suite.consumerCtx())
		if tc.expSlashPacket {
			// Check that slash packet is queued
			suite.Require().NotEmpty(pendingPackets, "test: "+tc.name+"; pending packets empty")
			suite.Require().Len(pendingPackets, 1, "test: "+tc.name+"; pending packets len should be 1 is %d", len(pendingPackets))
			cp := pendingPackets[0]
			suite.Require().Equal(ccv.SlashPacket, cp.Type, "test: "+tc.name)
			sp := cp.GetSlashPacketData()
			suite.Require().Equal(stakingtypes.Infraction_INFRACTION_DOWNTIME, sp.Infraction, "test: "+tc.name)
			suite.Require().Equal(vals[tc.targetValidator].Address, sp.Validator.Address, "test: "+tc.name)
		} else {
			suite.Require().Empty(pendingPackets, "test: "+tc.name+"; pending packets non-empty")
		}

		if i+1 < len(testCases) {
			// reset suite
			suite.SetupTest()
		}
	}
}

// slashingBeginBlocker is a mock for the slashing BeginBlocker.
// It applies the votes for a sequence of blocks
func slashingBeginBlocker(s *CCVTestSuite, votes []abci.VoteInfo, blocks int64) {
	consumerSlashingKeeper := s.consumerApp.GetTestSlashingKeeper()
	currentHeight := s.consumerCtx().BlockHeight()
	for s.consumerCtx().BlockHeight() < currentHeight+blocks {
		for _, voteInfo := range votes {
			consumerSlashingKeeper.HandleValidatorSignature(
				s.consumerCtx(),
				voteInfo.Validator.Address,
				voteInfo.Validator.Power,
				voteInfo.SignedLastBlock,
			)
		}
		s.consumerChain.NextBlock()
	}
}
