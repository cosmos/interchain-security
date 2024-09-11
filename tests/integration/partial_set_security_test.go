package integration

import (
	"slices"
	"sort"
	"testing"

	"github.com/stretchr/testify/require"

	"cosmossdk.io/math"

	appConsumer "github.com/cosmos/interchain-security/v6/app/consumer"
	appProvider "github.com/cosmos/interchain-security/v6/app/provider"
	icstestingutils "github.com/cosmos/interchain-security/v6/testutil/ibc_testing"
	"github.com/cosmos/interchain-security/v6/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/v6/x/ccv/types"
)

// we need a stake multiplier because tokens do not directly correspond to voting power
// this is needed because 1000000 tokens = 1 voting power, so lower multipliers
// will be verbose and harder to read because small token numbers
// won't correspond to at least one voting power
const stakeMultiplier = 1000000

// TestMinStake tests the min stake parameter.
// @Long Description@
// It starts a provider and single consumer chain,
// sets the initial powers according to the input, and then
// sets the min stake parameter according to the test case.
// Finally, it checks that the validator set on the consumer chain is as expected
// according to the min stake parameter.
func TestMinStake(t *testing.T) {
	testCases := []struct {
		name                string
		stakedTokens        []int64
		minStake            uint64
		expectedConsuValSet []int64
	}{
		{
			name: "disabled min stake",
			stakedTokens: []int64{
				1 * stakeMultiplier,
				2 * stakeMultiplier,
				3 * stakeMultiplier,
				4 * stakeMultiplier,
			},
			minStake: 0,
			expectedConsuValSet: []int64{
				1 * stakeMultiplier,
				2 * stakeMultiplier,
				3 * stakeMultiplier,
				4 * stakeMultiplier,
			},
		},
		{
			name: "stake multiplier - standard case",
			stakedTokens: []int64{
				1 * stakeMultiplier,
				2 * stakeMultiplier,
				3 * stakeMultiplier,
				4 * stakeMultiplier,
			},
			minStake: 3 * stakeMultiplier,
			expectedConsuValSet: []int64{
				3 * stakeMultiplier,
				4 * stakeMultiplier,
			},
		},
		{
			name: "check min stake with multiple equal stakes",
			stakedTokens: []int64{
				1 * stakeMultiplier,
				2 * stakeMultiplier,
				2 * stakeMultiplier,
				2 * stakeMultiplier,
			},
			minStake: 2 * stakeMultiplier,
			expectedConsuValSet: []int64{
				2 * stakeMultiplier,
				2 * stakeMultiplier,
				2 * stakeMultiplier,
			},
		},
	}
	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			s := NewCCVTestSuite[*appProvider.App, *appConsumer.App](
				// Pass in ibctesting.AppIniters for provider and consumer.
				icstestingutils.ProviderAppIniter, icstestingutils.ConsumerAppIniter, []string{})
			s.SetT(t)
			s.SetupTest()

			providerKeeper := s.providerApp.GetProviderKeeper()
			s.SetupCCVChannel(s.path)

			// set validator powers
			vals, err := providerKeeper.GetLastBondedValidators(s.providerChain.GetContext())
			s.Require().NoError(err)

			delegatorAccount := s.providerChain.SenderAccounts[0]

			for i, val := range vals {
				power := tc.stakedTokens[i]
				valAddr, err := providerKeeper.ValidatorAddressCodec().StringToBytes(val.GetOperator())
				s.Require().NoError(err)
				undelegate(s, delegatorAccount.SenderAccount.GetAddress(), valAddr, math.LegacyOneDec())

				// set validator power
				delegateByIdx(s, delegatorAccount.SenderAccount.GetAddress(), math.NewInt(power), i)
			}

			// end the epoch to apply the updates
			s.nextEpoch()

			// Relay 1 VSC packet from provider to consumer
			relayAllCommittedPackets(s, s.providerChain, s.path, ccv.ProviderPortID, s.path.EndpointB.ChannelID, 1)

			// end the block on the consumer to apply the updates
			s.consumerChain.NextBlock()

			// get the last bonded validators
			lastVals, err := providerKeeper.GetLastBondedValidators(s.providerChain.GetContext())
			s.Require().NoError(err)

			// Assuming tc.stakedTokens is defined somewhere in your test case
			// Create a copy of the tc.stakedTokens slice
			sortedTokens := make([]int64, len(tc.stakedTokens))
			copy(sortedTokens, tc.stakedTokens)

			// Sort the copied slice in descending order
			sort.Slice(sortedTokens, func(i, j int) bool {
				return sortedTokens[i] > sortedTokens[j]
			})

			for i, val := range lastVals {
				// check that the initial state was set correctly
				require.Equal(s.T(), math.NewInt(sortedTokens[i]), val.Tokens)
			}

			// check the validator set on the consumer chain is the original one
			consuValSet := s.consumerChain.LastHeader.ValidatorSet
			s.Require().Equal(len(consuValSet.Validators), 4)

			// get just the powers of the consu val set
			consuValPowers := make([]int64, len(consuValSet.Validators))
			for i, consuVal := range consuValSet.Validators {
				// voting power corresponds to staked tokens at a 1:stake_multiplier ratio
				consuValPowers[i] = consuVal.VotingPower * stakeMultiplier
			}

			s.Require().ElementsMatch(consuValPowers, tc.stakedTokens)

			// adjust parameters

			// set the minStake according to the test case
			err = providerKeeper.SetConsumerPowerShapingParameters(
				s.providerChain.GetContext(),
				s.getFirstBundle().ConsumerId,
				types.PowerShapingParameters{
					MinStake: tc.minStake,
				},
			)
			s.Require().NoError(err)

			// delegate and undelegate to trigger a vscupdate

			// first delegate
			delegateAndUndelegate(s, delegatorAccount.SenderAccount.GetAddress(), math.NewInt(1*stakeMultiplier), 1)

			// end the epoch to apply the updates
			s.nextEpoch()

			if slices.Equal(tc.stakedTokens, tc.expectedConsuValSet) {
				// don't expect to relay a packet
				relayAllCommittedPackets(s, s.providerChain, s.path, ccv.ProviderPortID, s.path.EndpointB.ChannelID, 0)
			} else {
				// Relay 1 VSC packet from provider to consumer
				relayAllCommittedPackets(s, s.providerChain, s.path, ccv.ProviderPortID, s.path.EndpointB.ChannelID, 1)
			}

			// end the block on the consumer to apply the updates
			s.consumerChain.NextBlock()

			// construct the new val powers
			newConsuValSet := s.consumerChain.LastHeader.ValidatorSet
			newConsuValPowers := make([]int64, len(newConsuValSet.Validators))
			for i, consuVal := range newConsuValSet.Validators {
				// voting power corresponds to staked tokens at a 1:stake_multiplier ratio
				newConsuValPowers[i] = consuVal.VotingPower * stakeMultiplier
			}

			// check that the new validator set is as expected
			s.Require().ElementsMatch(newConsuValPowers, tc.expectedConsuValSet)
		})
	}
}
