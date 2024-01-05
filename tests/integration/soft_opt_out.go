package integration

import (
	"bytes"
	"sort"

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
	testCases := []struct {
		name            string
		downtimeFunc    func(sdk.Context, *consumerKeeper.Keeper, *slashingkeeper.Keeper, []byte, int)
		targetValidator int
		expSlashPacket  bool
	}{
		{
			"donwtime top 95%",
			func(ctx sdk.Context, ck *consumerKeeper.Keeper, sk *slashingkeeper.Keeper, valAddr []byte, valIdx int) {
				val, found := ck.GetCCValidator(ctx, valAddr)
				suite.Require().True(found)
				// Let the validator stop signing s.t. a downtime event occurs.
				// Continue increasing the height until enough blocks are missed.
				downtimeHeight := ctx.BlockHeight() + sk.SignedBlocksWindow(ctx) - sk.MinSignedPerWindow(ctx)
				for height := ctx.BlockHeight(); height <= downtimeHeight; height++ {
					ctx = ctx.WithBlockHeight(height)
					sk.HandleValidatorSignature(ctx, val.Address, val.Power, false)
				}
			},
			0,
			true,
		},
		{
			"donwtime bottom 5%",
			func(ctx sdk.Context, ck *consumerKeeper.Keeper, sk *slashingkeeper.Keeper, valAddr []byte, valIdx int) {
				val, found := ck.GetCCValidator(ctx, valAddr)
				suite.Require().True(found)
				// Let the validator stop signing s.t. a downtime event occurs.
				// Continue increasing the height until enough blocks are missed.
				downtimeHeight := ctx.BlockHeight() + sk.SignedBlocksWindow(ctx) - sk.MinSignedPerWindow(ctx)
				for height := ctx.BlockHeight(); height <= downtimeHeight; height++ {
					ctx = ctx.WithBlockHeight(height)
					sk.HandleValidatorSignature(ctx, val.Address, val.Power, false)
				}
			},
			3,
			false,
		},
		{
			"donwtime bottom 5% first and then top 95%",
			func(ctx sdk.Context, ck *consumerKeeper.Keeper, sk *slashingkeeper.Keeper, valAddr []byte, valIdx int) {
				val, found := ck.GetCCValidator(ctx, valAddr)
				suite.Require().True(found)
				// Let the validator stop signing s.t. a downtime event occurs.
				// Continue increasing the height until enough blocks are missed.
				downtimeHeight := ctx.BlockHeight() + sk.SignedBlocksWindow(ctx) - sk.MinSignedPerWindow(ctx)
				height := ctx.BlockHeight()
				for ; height < downtimeHeight; height++ {
					ctx = ctx.WithBlockHeight(height)
					sk.HandleValidatorSignature(ctx, val.Address, val.Power, false)
				}

				// Increase the power of this validator (to bring it in the top 95%)
				delAddr := suite.providerChain.SenderAccount.GetAddress()
				bondAmt := sdk.NewInt(100).Mul(sdk.DefaultPowerReduction)
				delegateByIdx(suite, delAddr, bondAmt, valIdx)

				suite.providerChain.NextBlock()

				// Relay 1 VSC packet from provider to consumer
				relayAllCommittedPackets(suite, suite.providerChain, suite.path, ccv.ProviderPortID, suite.path.EndpointB.ChannelID, 1)

				// Update validator from store
				val, found = ck.GetCCValidator(ctx, valAddr)
				suite.Require().True(found)
				smallestNonOptOutPower := ck.GetSmallestNonOptOutPower(ctx)
				suite.Require().Equal(val.Power, smallestNonOptOutPower)

				// Let the validator continue not signing
				for ; height <= downtimeHeight; height++ {
					ctx = ctx.WithBlockHeight(height)
					sk.HandleValidatorSignature(ctx, val.Address, val.Power, false)
				}
			},
			2,
			false,
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

		// sync suite context after CCV channel is established
		ctx := suite.consumerCtx()

		// Check that the third validator is the first in the top 95%
		smallestNonOptOutPower := consumerKeeper.GetSmallestNonOptOutPower(ctx)
		suite.Require().Equal(validatorPowers[1], smallestNonOptOutPower, "test: "+tc.name)

		// Let everyone sign the first 100 blocks (default value for slahing.SignedBlocksWindow param).
		// This populates the signingInfo of the slashing module so that
		// the check for starting height passes.
		signedBlocksWindow := consumerSlashingKeeper.SignedBlocksWindow(ctx)
		height := int64(0)
		vals := consumerKeeper.GetAllCCValidator(ctx)
		// Note that GetAllCCValidator is iterating over a map so the result need to be sorted
		sort.Slice(vals, func(i, j int) bool {
			if vals[i].Power != vals[j].Power {
				return vals[i].Power > vals[j].Power
			}
			return bytes.Compare(vals[i].Address, vals[j].Address) > 0
		})
		for ; height < signedBlocksWindow; height++ {
			for _, val := range vals {
				// Note that the actual consumer height doesn't matter, but just the passed context
				ctx = ctx.WithBlockHeight(height)
				// In production, HandleValidatorSignature is called by the BeginBlocker of the slashing module
				consumerSlashingKeeper.HandleValidatorSignature(ctx, val.Address, val.Power, true)
			}
		}

		sk := consumerSlashingKeeper.(slashingkeeper.Keeper)
		tc.downtimeFunc(ctx, &consumerKeeper, &sk, vals[tc.targetValidator].Address, tc.targetValidator)

		// Get signing info for target validator
		consAddr := sdk.ConsAddress(vals[tc.targetValidator].Address)
		info, _ := consumerSlashingKeeper.GetValidatorSigningInfo(ctx, consAddr)
		// expect increased jail time
		suite.Require().True(
			info.JailedUntil.Equal(ctx.BlockTime().Add(consumerSlashingKeeper.DowntimeJailDuration(ctx))),
			"test: "+tc.name+"; did not update validator jailed until signing info",
		)
		// expect missed block counters reset
		suite.Require().Zero(info.MissedBlocksCounter, "test: "+tc.name+"; did not reset validator missed block counter")
		suite.Require().Zero(info.IndexOffset, "test: "+tc.name)
		consumerSlashingKeeper.IterateValidatorMissedBlockBitArray(ctx, consAddr, func(_ int64, missed bool) bool {
			suite.Require().True(missed, "test: "+tc.name)
			return false
		})

		pendingPackets := consumerKeeper.GetPendingPackets(ctx)
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
