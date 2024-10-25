package keeper_test

import (
	"bytes"
	"errors"
	"fmt"
	gomath "math"
	"sort"
	"testing"

	"cosmossdk.io/math"
	"github.com/cometbft/cometbft/proto/tendermint/crypto"
	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"
	"pgregory.net/rapid"

	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"
	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	testkeeper "github.com/cosmos/interchain-security/v6/testutil/keeper"
	"github.com/cosmos/interchain-security/v6/x/ccv/provider/keeper"
	providertypes "github.com/cosmos/interchain-security/v6/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/v6/x/ccv/types"
)

func TestHasMinPower(t *testing.T) {
	pk, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	providerConsPubKey := ed25519.GenPrivKeyFromSecret([]byte{1}).PubKey()
	consAddr := sdk.ConsAddress(providerConsPubKey.Address())
	providerAddr := providertypes.NewProviderConsAddress(consAddr)

	testCases := []struct {
		name        string
		minPower    uint64
		expectation func(sdk.ConsAddress, testkeeper.MockedKeepers)
		expError    bool
		hasMinPower bool
	}{
		{
			name: "cannot find validator by cons address",
			expectation: func(sdk.ConsAddress, testkeeper.MockedKeepers) {
				mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(gomock.Any(), consAddr).
					Return(stakingtypes.Validator{}, fmt.Errorf("validator not found")).Times(1)
			},
			expError:    true,
			hasMinPower: false,
		}, {
			name: "cannot convert validator operator address",
			expectation: func(consAddr sdk.ConsAddress, mocks testkeeper.MockedKeepers) {
				mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(gomock.Any(), consAddr).Return(stakingtypes.Validator{OperatorAddress: "xxxx"}, nil).Times(1)
			},
			expError:    true,
			hasMinPower: false,
		}, {
			name: "cannot find last validator power",
			expectation: func(consAddr sdk.ConsAddress, mocks testkeeper.MockedKeepers) {
				valAddr := sdk.ValAddress(providerAddr.Address.Bytes())
				mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(gomock.Any(), consAddr).
					Return(stakingtypes.Validator{OperatorAddress: valAddr.String()}, nil)
				mocks.MockStakingKeeper.EXPECT().GetLastValidatorPower(gomock.Any(), valAddr).
					Return(int64(0), fmt.Errorf("last power not found")).Times(1)
			},
			expError:    true,
			hasMinPower: false,
		}, {
			name: "validator power is LT min power",
			expectation: func(consAddr sdk.ConsAddress, mocks testkeeper.MockedKeepers) {
				valAddr := sdk.ValAddress(providerAddr.Address.Bytes())
				mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(gomock.Any(), consAddr).
					Return(stakingtypes.Validator{OperatorAddress: valAddr.String()}, nil)
				mocks.MockStakingKeeper.EXPECT().GetLastValidatorPower(gomock.Any(), valAddr).
					Return(int64(5), nil).Times(1)
			},
			expError:    false,
			hasMinPower: false,
		}, {
			name: "validator power is GTE min power",
			expectation: func(consAddr sdk.ConsAddress, mocks testkeeper.MockedKeepers) {
				valAddr := sdk.ValAddress(providerAddr.Address.Bytes())
				mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(gomock.Any(), consAddr).
					Return(stakingtypes.Validator{OperatorAddress: valAddr.String()}, nil)
				mocks.MockStakingKeeper.EXPECT().GetLastValidatorPower(gomock.Any(), valAddr).
					Return(int64(10), nil).Times(1)
			},
			expError:    false,
			hasMinPower: true,
		},
	}

	minPower := int64(10)

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			tc.expectation(consAddr, mocks)
			hasMinPower, err := pk.HasMinPower(ctx, providerAddr, minPower)
			if tc.expError {
				require.Error(t, err)
			} else {
				require.NoError(t, err)
			}
			require.Equal(t, tc.hasMinPower, hasMinPower)
		})
	}
}

func TestComputeMinPowerInTopN(t *testing.T) {
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	// create 5 validators with powers 1, 3, 5, 6, 10 (not in that order) with total power of 25 (= 1 + 3 + 5 + 6 + 10)
	// such that:
	// validator power => cumulative share
	// 10 => 40%
	// 6 => 64%
	// 5 => 84%
	// 3 => 96%
	// 1 => 100%

	bondedValidators := []stakingtypes.Validator{
		createStakingValidator(ctx, mocks, 5, 1),
		createStakingValidator(ctx, mocks, 10, 2),
		createStakingValidator(ctx, mocks, 3, 3),
		createStakingValidator(ctx, mocks, 1, 4),
		createStakingValidator(ctx, mocks, 6, 5),
	}

	m, err := providerKeeper.ComputeMinPowerInTopN(ctx, bondedValidators, 100)
	require.NoError(t, err)
	require.Equal(t, int64(1), m)

	m, err = providerKeeper.ComputeMinPowerInTopN(ctx, bondedValidators, 97)
	require.NoError(t, err)
	require.Equal(t, int64(1), m)

	m, err = providerKeeper.ComputeMinPowerInTopN(ctx, bondedValidators, 96)
	require.NoError(t, err)
	require.Equal(t, int64(3), m)

	m, err = providerKeeper.ComputeMinPowerInTopN(ctx, bondedValidators, 85)
	require.NoError(t, err)
	require.Equal(t, int64(3), m)

	m, err = providerKeeper.ComputeMinPowerInTopN(ctx, bondedValidators, 84)
	require.NoError(t, err)
	require.Equal(t, int64(5), m)

	m, err = providerKeeper.ComputeMinPowerInTopN(ctx, bondedValidators, 65)
	require.NoError(t, err)
	require.Equal(t, int64(5), m)

	m, err = providerKeeper.ComputeMinPowerInTopN(ctx, bondedValidators, 64)
	require.NoError(t, err)
	require.Equal(t, int64(6), m)

	m, err = providerKeeper.ComputeMinPowerInTopN(ctx, bondedValidators, 50)
	require.NoError(t, err)
	require.Equal(t, int64(6), m)

	m, err = providerKeeper.ComputeMinPowerInTopN(ctx, bondedValidators, 40)
	require.NoError(t, err)
	require.Equal(t, int64(10), m)

	m, err = providerKeeper.ComputeMinPowerInTopN(ctx, bondedValidators, 1)
	require.NoError(t, err)
	require.Equal(t, int64(10), m)

	_, err = providerKeeper.ComputeMinPowerInTopN(ctx, bondedValidators, 0)
	require.Error(t, err)

	_, err = providerKeeper.ComputeMinPowerInTopN(ctx, bondedValidators, 101)
	require.Error(t, err)
}

// TestCanValidateChain returns true if `validator` is opted in, in `consumerId.
func TestCanValidateChain(t *testing.T) {
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	consumerID := "0"

	validator := createStakingValidator(ctx, mocks, 1, 1) // adds GetLastValidatorPower expectation to mocks
	consAddr, _ := validator.GetConsAddr()
	providerAddr := providertypes.NewProviderConsAddress(consAddr)

	// with no allowlist or denylist, the validator has to be opted in, in order to consider it
	powerShapingParameters, err := providerKeeper.GetConsumerPowerShapingParameters(ctx, consumerID)
	require.Error(t, err)
	canValidateChain, err := providerKeeper.CanValidateChain(ctx, consumerID, providerAddr, powerShapingParameters.Top_N, 0)
	require.NoError(t, err)
	require.False(t, canValidateChain)

	// with TopN chains, the validator can be considered,
	mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(gomock.Any(), providerAddr.Address).Return(validator, nil).Times(2)
	err = providerKeeper.SetConsumerPowerShapingParameters(ctx, consumerID, providertypes.PowerShapingParameters{Top_N: 50})
	require.NoError(t, err)
	powerShapingParameters, err = providerKeeper.GetConsumerPowerShapingParameters(ctx, consumerID)
	require.NoError(t, err)
	// validator's power is LT the min power
	canValidateChain, err = providerKeeper.CanValidateChain(ctx, consumerID, providerAddr, powerShapingParameters.Top_N, 2)
	require.NoError(t, err)
	require.False(t, canValidateChain)
	// validator's power is GTE the min power
	canValidateChain, err = providerKeeper.CanValidateChain(ctx, consumerID, providerAddr, powerShapingParameters.Top_N, 1)
	require.NoError(t, err)
	require.True(t, canValidateChain)

	// when validator is opted-in it can validate regardless of its min power
	providerKeeper.SetOptedIn(ctx, consumerID, providertypes.NewProviderConsAddress(consAddr))
	canValidateChain, err = providerKeeper.CanValidateChain(ctx, consumerID, providerAddr, powerShapingParameters.Top_N, 2)
	require.NoError(t, err)
	require.True(t, canValidateChain)

	// With OptIn chains, validator can validate only if it has already opted-in
	err = providerKeeper.SetConsumerPowerShapingParameters(ctx, consumerID, providertypes.PowerShapingParameters{Top_N: 0})
	require.NoError(t, err)
	powerShapingParameters, err = providerKeeper.GetConsumerPowerShapingParameters(ctx, consumerID)
	require.NoError(t, err)
	canValidateChain, err = providerKeeper.CanValidateChain(ctx, consumerID, providerAddr, powerShapingParameters.Top_N, 2)
	require.NoError(t, err)
	require.True(t, canValidateChain)

	// create an allow list but do not add the validator `providerAddr` to it
	validatorA := createStakingValidator(ctx, mocks, 1, 2)
	consAddrA, _ := validatorA.GetConsAddr()
	providerKeeper.SetAllowlist(ctx, consumerID, providertypes.NewProviderConsAddress(consAddrA))
	canValidateChain, err = providerKeeper.CanValidateChain(ctx, consumerID, providerAddr, powerShapingParameters.Top_N, 1)
	require.NoError(t, err)
	require.False(t, canValidateChain)
	providerKeeper.SetAllowlist(ctx, consumerID, providertypes.NewProviderConsAddress(consAddr))
	canValidateChain, err = providerKeeper.CanValidateChain(ctx, consumerID, providerAddr, powerShapingParameters.Top_N, 1)
	require.NoError(t, err)
	require.True(t, canValidateChain)

	// create a denylist but do not add validator `providerAddr` to it
	providerKeeper.SetDenylist(ctx, consumerID, providertypes.NewProviderConsAddress(consAddrA))
	canValidateChain, err = providerKeeper.CanValidateChain(ctx, consumerID, providerAddr, powerShapingParameters.Top_N, 1)
	require.NoError(t, err)
	require.True(t, canValidateChain)
	// add validator `providerAddr` to the denylist
	providerKeeper.SetDenylist(ctx, consumerID, providertypes.NewProviderConsAddress(consAddr))
	canValidateChain, err = providerKeeper.CanValidateChain(ctx, consumerID, providerAddr, powerShapingParameters.Top_N, 1)
	require.NoError(t, err)
	require.False(t, canValidateChain)
}

func TestCapValidatorSet(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	valAddrA := "cosmosvalcons1ezyrq65s3gshhx5585w6mpusq3xsj3ayzf4uv6"
	valAddrB := "cosmosvalcons1nx7n5uh0ztxsynn4sje6eyq2ud6rc6klc96w39"
	valAddrC := "cosmosvalcons1qmq08eruchr5sf5s3rwz7djpr5a25f7xw4mceq"
	valAddrD := "cosmosvalcons1kswr5sq599365kcjmhgufevfps9njf43e4lwdk"

	validatorA := providertypes.ConsensusValidator{ProviderConsAddr: consAddressFromBech32(valAddrA), Power: 1, PublicKey: &crypto.PublicKey{}}
	validatorB := providertypes.ConsensusValidator{ProviderConsAddr: consAddressFromBech32(valAddrB), Power: 2, PublicKey: &crypto.PublicKey{}}
	validatorC := providertypes.ConsensusValidator{ProviderConsAddr: consAddressFromBech32(valAddrC), Power: 3, PublicKey: &crypto.PublicKey{}}
	validatorD := providertypes.ConsensusValidator{ProviderConsAddr: consAddressFromBech32(valAddrD), Power: 4, PublicKey: &crypto.PublicKey{}}
	validators := []providertypes.ConsensusValidator{validatorA, validatorB, validatorC, validatorD}

	// Initial error check
	powerShapingParameters, err := providerKeeper.GetConsumerPowerShapingParameters(ctx, CONSUMER_ID)
	require.Error(t, err)
	priorityValidators, nonPriorityValidators := providerKeeper.PartitionBasedOnPriorityList(ctx, CONSUMER_ID, validators)
	consumerValidators := providerKeeper.CapValidatorSet(ctx, powerShapingParameters, append(priorityValidators, nonPriorityValidators...))
	require.Equal(t, []providertypes.ConsensusValidator{validatorD, validatorC, validatorB, validatorA}, consumerValidators)

	testCases := []struct {
		name                   string
		powerShapingParameters providertypes.PowerShapingParameters
		expectedValidators     []providertypes.ConsensusValidator
		expectError            bool
	}{
		{
			name:                   "ValidatorSetCap = 0 (no capping)",
			powerShapingParameters: providertypes.PowerShapingParameters{ValidatorSetCap: 0},
			expectedValidators:     []providertypes.ConsensusValidator{validatorD, validatorC, validatorB, validatorA},
		},
		{
			name: "ValidatorSetCap = 0, with priority list",
			powerShapingParameters: providertypes.PowerShapingParameters{
				ValidatorSetCap: 0,
				Prioritylist: []string{
					valAddrA,
					valAddrB,
				},
			},
			expectedValidators: []providertypes.ConsensusValidator{validatorB, validatorA, validatorD, validatorC},
		},
		{
			name:                   "ValidatorSetCap > len(validators) (no capping)",
			powerShapingParameters: providertypes.PowerShapingParameters{ValidatorSetCap: 100},
			expectedValidators:     []providertypes.ConsensusValidator{validatorD, validatorC, validatorB, validatorA},
		},
		{
			name:                   "ValidatorSetCap = 1 (capping to highest power, no priority list)",
			powerShapingParameters: providertypes.PowerShapingParameters{ValidatorSetCap: 1},
			expectedValidators:     []providertypes.ConsensusValidator{validatorD},
		},
		{
			name:                   "ValidatorSetCap = 2 (capping to two highest power, no priority list)",
			powerShapingParameters: providertypes.PowerShapingParameters{ValidatorSetCap: 2},
			expectedValidators:     []providertypes.ConsensusValidator{validatorD, validatorC},
		},
		{
			name:                   "ValidatorSetCap = 3 (capping to three highest power, no priority list)",
			powerShapingParameters: providertypes.PowerShapingParameters{ValidatorSetCap: 3},
			expectedValidators:     []providertypes.ConsensusValidator{validatorD, validatorC, validatorB},
		},
		{
			name: "ValidatorSetCap = 2, with priority list",
			powerShapingParameters: providertypes.PowerShapingParameters{
				ValidatorSetCap: 2,
				Prioritylist: []string{
					valAddrA,
					valAddrB,
				},
			},
			expectedValidators: []providertypes.ConsensusValidator{validatorB, validatorA},
		},
		{
			name: "ValidatorSetCap = 3, with partial priority list",
			powerShapingParameters: providertypes.PowerShapingParameters{
				ValidatorSetCap: 3,
				Prioritylist:    []string{valAddrA},
			},
			expectedValidators: []providertypes.ConsensusValidator{validatorA, validatorD, validatorC},
		},
		{
			name: "All validators in priority list",
			powerShapingParameters: providertypes.PowerShapingParameters{
				ValidatorSetCap: 4,
				Prioritylist: []string{
					valAddrC,
					valAddrA,
					valAddrD,
					valAddrB,
				},
			},
			expectedValidators: []providertypes.ConsensusValidator{validatorD, validatorC, validatorB, validatorA},
		},
		{
			name: "ValidatorSetCap = 1 (capping to highest power, with priority list)",
			powerShapingParameters: providertypes.PowerShapingParameters{
				ValidatorSetCap: 1,
				Prioritylist:    []string{valAddrA},
			},
			expectedValidators: []providertypes.ConsensusValidator{validatorA},
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			err := providerKeeper.SetConsumerPowerShapingParameters(ctx, CONSUMER_ID, tc.powerShapingParameters)
			require.NoError(t, err)

			powerShapingParameters, err := providerKeeper.GetConsumerPowerShapingParameters(ctx, CONSUMER_ID)
			if tc.expectError {
				require.Error(t, err)
			} else {
				require.NoError(t, err)
				require.Equal(t, tc.powerShapingParameters, powerShapingParameters)
			}
			priorityValidators, nonPriorityValidators := providerKeeper.PartitionBasedOnPriorityList(ctx, CONSUMER_ID, validators)
			consumerValidators := providerKeeper.CapValidatorSet(ctx, powerShapingParameters, append(priorityValidators, nonPriorityValidators...))
			require.Equal(t, tc.expectedValidators, consumerValidators)
		})
	}
}

// Helper function to handle address conversion
func consAddressFromBech32(addr string) sdk.ConsAddress {
	consAddr, err := sdk.ConsAddressFromBech32(addr)
	if err != nil {
		panic(fmt.Sprintf("invalid consensus address: %s", addr))
	}
	return consAddr
}

func TestCapValidatorsPower(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	validatorA := providertypes.ConsensusValidator{
		ProviderConsAddr: []byte("providerConsAddrA"),
		Power:            1,
		PublicKey:        &crypto.PublicKey{},
	}

	validatorB := providertypes.ConsensusValidator{
		ProviderConsAddr: []byte("providerConsAddrB"),
		Power:            2,
		PublicKey:        &crypto.PublicKey{},
	}

	validatorC := providertypes.ConsensusValidator{
		ProviderConsAddr: []byte("providerConsAddrC"),
		Power:            3,
		PublicKey:        &crypto.PublicKey{},
	}

	validatorD := providertypes.ConsensusValidator{
		ProviderConsAddr: []byte("providerConsAddrD"),
		Power:            4,
		PublicKey:        &crypto.PublicKey{},
	}

	validators := []providertypes.ConsensusValidator{validatorA, validatorB, validatorC, validatorD}

	expectedValidators := make([]providertypes.ConsensusValidator, len(validators))
	copy(expectedValidators, validators)
	expectedValidators[0].Power = 2
	expectedValidators[1].Power = 2
	expectedValidators[2].Power = 3
	expectedValidators[3].Power = 3

	sortValidators := func(validators []providertypes.ConsensusValidator) {
		sort.Slice(validators, func(i, j int) bool {
			return bytes.Compare(validators[i].ProviderConsAddr, validators[j].ProviderConsAddr) < 0
		})
	}

	// no capping takes place because validators power-cap is not set
	powerShapingParameters, err := providerKeeper.GetConsumerPowerShapingParameters(ctx, CONSUMER_ID)
	require.Error(t, err)
	cappedValidators := providerKeeper.CapValidatorsPower(ctx, powerShapingParameters.ValidatorsPowerCap, validators)
	sortValidators(validators)
	sortValidators(cappedValidators)
	require.Equal(t, validators, cappedValidators)

	err = providerKeeper.SetConsumerPowerShapingParameters(ctx, CONSUMER_ID, providertypes.PowerShapingParameters{
		ValidatorsPowerCap: 33,
	})
	require.NoError(t, err)
	powerShapingParameters, err = providerKeeper.GetConsumerPowerShapingParameters(ctx, CONSUMER_ID)
	require.NoError(t, err)
	cappedValidators = providerKeeper.CapValidatorsPower(ctx, powerShapingParameters.ValidatorsPowerCap, validators)
	sortValidators(expectedValidators)
	sortValidators(cappedValidators)
	require.Equal(t, expectedValidators, cappedValidators)
}

func TestNoMoreThanPercentOfTheSum(t *testing.T) {
	// **impossible** case where we only have 9 powers, and we want that no number has more than 10% of the total sum
	powers := []int64{1, 2, 3, 4, 5, 6, 7, 8, 9}
	percent := uint32(10)
	require.False(t, noMoreThanPercent(keeper.NoMoreThanPercentOfTheSum(createConsumerValidators(powers), percent), percent))

	powers = []int64{1, 2, 3, 4, 5}
	percent = 20
	require.True(t, noMoreThanPercent(keeper.NoMoreThanPercentOfTheSum(createConsumerValidators(powers), percent), percent))

	powers = []int64{1, 2, 3, 4, 5}
	percent = 21
	require.True(t, noMoreThanPercent(keeper.NoMoreThanPercentOfTheSum(createConsumerValidators(powers), percent), percent))

	powers = []int64{1, 2, 3, 4, 5}
	percent = 25
	require.True(t, noMoreThanPercent(keeper.NoMoreThanPercentOfTheSum(createConsumerValidators(powers), percent), percent))

	powers = []int64{1, 2, 3, 4, 5}
	percent = 32
	require.True(t, noMoreThanPercent(keeper.NoMoreThanPercentOfTheSum(createConsumerValidators(powers), percent), percent))

	powers = []int64{1, 2, 3, 4, 5}
	percent = 33
	require.True(t, noMoreThanPercent(keeper.NoMoreThanPercentOfTheSum(createConsumerValidators(powers), percent), percent))

	powers = []int64{1, 2, 3, 4, 5}
	percent = 34
	require.True(t, noMoreThanPercent(keeper.NoMoreThanPercentOfTheSum(createConsumerValidators(powers), percent), percent))

	powers = []int64{1, 2, 3, 4, 5}
	percent = 50
	require.True(t, noMoreThanPercent(keeper.NoMoreThanPercentOfTheSum(createConsumerValidators(powers), percent), percent))
}

func createConsumerValidators(powers []int64) []providertypes.ConsensusValidator {
	var validators []providertypes.ConsensusValidator
	for _, p := range powers {
		validators = append(validators, providertypes.ConsensusValidator{
			ProviderConsAddr: []byte("providerConsAddr"),
			Power:            p,
			PublicKey:        &crypto.PublicKey{},
		})
	}
	return validators
}

// returns `true` if no validator in `validators` corresponds to more than `percent` of the total sum of all
// validators' powers
func noMoreThanPercent(validators []providertypes.ConsensusValidator, percent uint32) bool {
	sum := int64(0)
	for _, v := range validators {
		sum += v.Power
	}

	for _, v := range validators {
		if float64(v.Power)*100.0 > float64(percent)*float64(sum) {
			return false
		}
	}
	return true
}

func sumPowers(vals []providertypes.ConsensusValidator) int64 {
	sum := int64(0)
	for _, v := range vals {
		sum += v.Power
	}
	return sum
}

func CapSatisfiable(vals []providertypes.ConsensusValidator, percent uint32) bool {
	// 100 / len(vals) is what each validator gets if each has the same power.
	// if this is more than the cap, it cannot be satisfied.
	return float64(100)/float64(len(vals)) < float64(percent)
}

func TestNoMoreThanPercentOfTheSumProps(t *testing.T) {
	// define properties to test

	// capRespectedIfSatisfiable: if the cap can be respected, then it will be respected
	capRespectedIfSatisfiable := func(valsBefore, valsAfter []providertypes.ConsensusValidator, percent uint32) bool {
		if CapSatisfiable(valsBefore, percent) {
			return noMoreThanPercent(valsAfter, percent)
		}
		return true
	}

	evenPowersIfCapCannotBeSatisfied := func(valsBefore, valsAfter []providertypes.ConsensusValidator, percent uint32) bool {
		if !CapSatisfiable(valsBefore, percent) {
			// if the cap cannot be satisfied, each validator should have the same power
			for _, valAfter := range valsAfter {
				if valAfter.Power != valsAfter[0].Power {
					return false
				}
			}
		}
		return true
	}

	// fairness: if before, v1 has more power than v2, then afterwards v1 will not have less power than v2
	// (they might get the same power if they are both capped)
	fairness := func(valsBefore, valsAfter []providertypes.ConsensusValidator) bool {
		for i, v := range valsBefore {
			// find the validator after with the same address
			vAfter := findConsumerValidator(t, v, valsAfter)

			// go through all other validators before (after this one, to avoid double checking)
			for j := i + 1; j < len(valsBefore); j++ {
				otherV := valsBefore[j]
				otherVAfter := findConsumerValidator(t, otherV, valsAfter)

				// v has at least as much power before
				if v.Power >= otherV.Power {
					// then otherV should not have more power after
					if vAfter.Power < otherVAfter.Power {
						return false
					}
				} else {
					// v has less power before
					// then v should not have more power after
					if vAfter.Power > otherVAfter.Power {
						return false
					}
				}
			}
		}
		return true
	}

	// non-zero: v has non-zero power before IFF it has non-zero power after
	nonZero := func(valsBefore, valsAfter []providertypes.ConsensusValidator) bool {
		for _, v := range valsBefore {
			vAfter := findConsumerValidator(t, v, valsAfter)
			if (v.Power == 0) != (vAfter.Power == 0) {
				return false
			}
		}
		return true
	}

	// equalSumIfCapSatisfiable: the sum of the powers of the validators will not change if the cap can be satisfied
	// (except for small changes by rounding errors)
	equalSumIfCapSatisfiable := func(valsBefore, valsAfter []providertypes.ConsensusValidator, percent uint32) bool {
		if CapSatisfiable(valsBefore, percent) {
			difference := gomath.Abs(float64(sumPowers(valsBefore) - sumPowers(valsAfter)))
			if difference > 1 {
				// if the difference is more than a rounding error, they are not equal
				return false
			}
		}
		return true
	}

	// num validators: the number of validators will not change
	equalNumVals := func(valsBefore, valsAfter []providertypes.ConsensusValidator) bool {
		return len(valsBefore) == len(valsAfter)
	}

	// test setup for pbt
	rapid.Check(t, func(t *rapid.T) {
		powers := rapid.SliceOf(rapid.Int64Range(1, 1000000000000)).Draw(t, "powers")
		percent := uint32(rapid.Int32Range(1, 100).Draw(t, "percent"))

		consumerValidators := createConsumerValidators(powers)
		cappedValidators := keeper.NoMoreThanPercentOfTheSum(consumerValidators, percent)

		t.Log("can the cap be satisfied: ", CapSatisfiable(consumerValidators, percent))
		t.Log("before: ", consumerValidators)
		t.Log("after: ", cappedValidators)

		// check properties
		require.True(t, capRespectedIfSatisfiable(consumerValidators, cappedValidators, percent))
		require.True(t, evenPowersIfCapCannotBeSatisfied(consumerValidators, cappedValidators, percent))
		require.True(t, fairness(consumerValidators, cappedValidators))
		require.True(t, nonZero(consumerValidators, cappedValidators))
		require.True(t, equalSumIfCapSatisfiable(consumerValidators, cappedValidators, percent), "sum before: %v, sum after: %v", sumPowers(consumerValidators), sumPowers(cappedValidators))
		require.True(t, equalNumVals(consumerValidators, cappedValidators), "num before: %v, num after: %v", len(consumerValidators), len(cappedValidators))
	})
}

func findConsumerValidator(t *testing.T, v providertypes.ConsensusValidator, valsAfter []providertypes.ConsensusValidator) *providertypes.ConsensusValidator {
	t.Helper()

	index := -1
	for i, vA := range valsAfter {
		if bytes.Equal(v.ProviderConsAddr, vA.ProviderConsAddr) {
			index = i
			break
		}
	}
	if index == -1 {
		t.Fatalf("could not find validator with address %v in validators after \n validators after capping: %v", v.ProviderConsAddr, valsAfter)
	}
	return &valsAfter[index]
}

func createStakingValidatorsAndMocks(ctx sdk.Context, mocks testkeeper.MockedKeepers, powers ...int64) ([]stakingtypes.Validator, []providertypes.ProviderConsAddress) {
	var validators []stakingtypes.Validator
	for i, power := range powers {
		val := createStakingValidator(ctx, mocks, power, i)
		val.Tokens = math.NewInt(power)
		val.Status = stakingtypes.Bonded
		validators = append(validators, val)
	}

	var consAddrs []providertypes.ProviderConsAddress
	for _, val := range validators {
		consAddr, err := val.GetConsAddr()
		if err != nil {
			panic(err)
		}
		consAddrs = append(consAddrs, providertypes.NewProviderConsAddress(consAddr))
	}
	// set up mocks
	for index, val := range validators {
		mocks.MockStakingKeeper.EXPECT().GetValidatorByConsAddr(ctx, consAddrs[index].Address).Return(val, nil).AnyTimes()
	}

	return validators, consAddrs
}

// TestFulfillsMinStake checks that FulfillsMinStake returns true if the validator has at least the min stake
// and false otherwise
func TestFulfillsMinStake(t *testing.T) {
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	// create two validators with powers 1 and 2
	_, consAddrs := createStakingValidatorsAndMocks(ctx, mocks, 1, 2)

	testCases := []struct {
		name            string
		minStake        uint64
		expectedFulfill []bool
	}{
		{
			name:            "No min stake",
			minStake:        0,
			expectedFulfill: []bool{true, true},
		},
		{
			name:            "Min stake set to 2",
			minStake:        2,
			expectedFulfill: []bool{false, true},
		},
		{
			name:            "Min stake set to 3",
			minStake:        3,
			expectedFulfill: []bool{false, false},
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			for i, valAddr := range consAddrs {
				result, err := providerKeeper.FulfillsMinStake(ctx, tc.minStake, valAddr)
				require.NoError(t, err)
				require.Equal(t, tc.expectedFulfill[i], result)
			}
		})
	}
}

// TestIfInactiveValsDisallowedProperty checks that the number of validators in the next validator set is at most
// the MaxProviderConsensusValidators parameter if the consumer chain does not allow inactive validators to validate.
func TestIfInactiveValsDisallowedProperty(t *testing.T) {
	rapid.Check(t, func(r *rapid.T) {
		providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
		defer ctrl.Finish()

		// Generate a random number of validators with random powers
		valPowers := rapid.SliceOfN(rapid.Int64Range(1, 100), 1, 100).Draw(r, "valPowers")
		vals, consAddrs := createStakingValidatorsAndMocks(ctx, mocks, valPowers...)

		// opt the validators in
		for _, valAddr := range consAddrs {
			providerKeeper.SetOptedIn(ctx, CONSUMER_ID, valAddr)
		}

		// Randomly choose values for parameters
		minStake := rapid.Uint64Range(0, 101).Draw(r, "minStake")
		maxProviderConsensusVals := rapid.Uint32Range(1, 11).Draw(r, "maxProviderConsensusVals")

		// Set up the parameters in the provider keeper

		// do not allow inactive validators
		err := providerKeeper.SetConsumerPowerShapingParameters(ctx, CONSUMER_ID, providertypes.PowerShapingParameters{
			MinStake:          minStake,
			AllowInactiveVals: false,
		})
		require.NoError(t, err)
		params := providerKeeper.GetParams(ctx)
		params.MaxProviderConsensusValidators = int64(maxProviderConsensusVals)
		providerKeeper.SetParams(ctx, params)

		powerShapingParameters, err := providerKeeper.GetConsumerPowerShapingParameters(ctx, CONSUMER_ID)
		require.NoError(t, err)

		// Compute the next validators
		nextVals, err := providerKeeper.ComputeNextValidators(ctx, CONSUMER_ID, vals, powerShapingParameters, 0)
		require.NoError(t, err)

		// Check that the length of nextVals is at most maxProviderConsensusVals
		require.LessOrEqual(r, len(nextVals), int(maxProviderConsensusVals), "The length of nextVals should be at most maxProviderConsensusVals")

		// Sanity check: we only get 0 next validators if either:
		// - maxProviderConsensusVals is 0
		// - the maximal validator power is less than the min stake
		if len(nextVals) == 0 {
			maxValPower := int64(0)
			for _, power := range valPowers {
				if power > maxValPower {
					maxValPower = power
				}
			}
			require.True(
				r,
				maxProviderConsensusVals == 0 || maxValPower < int64(minStake),
				"The length of nextVals should only be 0 if either maxProviderConsensusVals is 0 or the maximal validator power is less than the min stake",
			)
		}
	})
}

// TestConsumerPowerShapingParameters tests the getter and setter of the consumer id to power-shaping parameters methods
func TestConsumerPowerShapingParameters(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	consumerId := CONSUMER_ID
	consAddrs := []string{
		"cosmosvalcons1kswr5sq599365kcjmhgufevfps9njf43e4lwdk",
		"cosmosvalcons1ezyrq65s3gshhx5585w6mpusq3xsj3ayzf4uv6",
		"cosmosvalcons1muys5jyqk4xd27e208nym85kn0t4zjcfeu63fe",
		"cosmosvalcons1nx7n5uh0ztxsynn4sje6eyq2ud6rc6klc96w39",
		"cosmosvalcons1qmq08eruchr5sf5s3rwz7djpr5a25f7xw4mceq",
		"cosmosvalcons1uuec3cjxajv5te08p220usrjhkfhg9wyvqn0tm",
	}
	providerConsAddr := []providertypes.ProviderConsAddress{}
	for _, addr := range consAddrs {
		ca, _ := sdk.ConsAddressFromBech32(addr)
		providerConsAddr = append(providerConsAddr, providertypes.NewProviderConsAddress(ca))
	}
	sortProviderConsAddr := func(consAddrs []providertypes.ProviderConsAddress) {
		sort.Slice(consAddrs, func(i, j int) bool {
			return bytes.Compare(consAddrs[i].Address, consAddrs[j].Address) < 0
		})
	}

	_, err := providerKeeper.GetConsumerPowerShapingParameters(ctx, consumerId)
	require.Error(t, err)
	require.True(t, errors.Is(err, ccvtypes.ErrStoreKeyNotFound))

	expectedPowerShapingParameters := providertypes.PowerShapingParameters{
		Top_N:              10,
		ValidatorsPowerCap: 34,
		ValidatorSetCap:    10,
		Allowlist:          []string{consAddrs[0], consAddrs[1]},
		Denylist:           []string{consAddrs[2], consAddrs[3]},
		MinStake:           234,
		AllowInactiveVals:  true,
		Prioritylist:       []string{consAddrs[1]},
	}
	expectedAllowlist := []providertypes.ProviderConsAddress{providerConsAddr[0], providerConsAddr[1]}
	sortProviderConsAddr(expectedAllowlist)
	expectedDenylist := []providertypes.ProviderConsAddress{providerConsAddr[2], providerConsAddr[3]}
	sortProviderConsAddr(expectedDenylist)
	expectedPrioritylist := []providertypes.ProviderConsAddress{providerConsAddr[1]}
	sortProviderConsAddr(expectedPrioritylist)
	err = providerKeeper.SetConsumerPowerShapingParameters(ctx, consumerId, expectedPowerShapingParameters)
	require.NoError(t, err)
	actualPowerShapingParameters, err := providerKeeper.GetConsumerPowerShapingParameters(ctx, consumerId)
	require.NoError(t, err)
	require.Equal(t, expectedPowerShapingParameters, actualPowerShapingParameters)
	require.Equal(t, expectedAllowlist, providerKeeper.GetAllowList(ctx, consumerId))
	require.Equal(t, expectedDenylist, providerKeeper.GetDenyList(ctx, consumerId))
	require.Equal(t, expectedPrioritylist, providerKeeper.GetPriorityList(ctx, consumerId))

	// assert that overwriting the current initialization record works
	expectedPowerShapingParameters = providertypes.PowerShapingParameters{
		Top_N:              12,
		ValidatorsPowerCap: 67,
		ValidatorSetCap:    20,
		Allowlist:          []string{consAddrs[4], consAddrs[5]},
		Denylist:           []string{consAddrs[2], consAddrs[3]},
		MinStake:           567,
		AllowInactiveVals:  false,
		Prioritylist:       []string{consAddrs[4], consAddrs[5]},
	}
	expectedAllowlist = []providertypes.ProviderConsAddress{providerConsAddr[4], providerConsAddr[5]}
	sortProviderConsAddr(expectedAllowlist)
	expectedDenylist = []providertypes.ProviderConsAddress{providerConsAddr[2], providerConsAddr[3]}
	sortProviderConsAddr(expectedDenylist)
	expectedPrioritylist = []providertypes.ProviderConsAddress{providerConsAddr[4], providerConsAddr[5]}
	sortProviderConsAddr(expectedAllowlist)
	err = providerKeeper.SetConsumerPowerShapingParameters(ctx, consumerId, expectedPowerShapingParameters)
	require.NoError(t, err)
	actualPowerShapingParameters, err = providerKeeper.GetConsumerPowerShapingParameters(ctx, consumerId)
	require.NoError(t, err)
	require.Equal(t, expectedPowerShapingParameters, actualPowerShapingParameters)
	require.Equal(t, expectedAllowlist, providerKeeper.GetAllowList(ctx, consumerId))
	require.Equal(t, expectedDenylist, providerKeeper.GetDenyList(ctx, consumerId))
	require.Equal(t, expectedPrioritylist, providerKeeper.GetPriorityList(ctx, consumerId))
}

// TestAllowlist tests the `SetAllowlist`, `IsAllowlisted`, `DeleteAllowlist`, and `IsAllowlistEmpty` methods
func TestAllowlist(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	consumerID := CONSUMER_ID

	// no validator was allowlisted and hence the allowlist is empty
	require.True(t, providerKeeper.IsAllowlistEmpty(ctx, consumerID))

	providerAddr1 := providertypes.NewProviderConsAddress([]byte("providerAddr1"))
	providerKeeper.SetAllowlist(ctx, consumerID, providerAddr1)
	require.True(t, providerKeeper.IsAllowlisted(ctx, consumerID, providerAddr1))

	// allowlist is not empty anymore
	require.False(t, providerKeeper.IsAllowlistEmpty(ctx, consumerID))

	providerAddr2 := providertypes.NewProviderConsAddress([]byte("providerAddr2"))
	providerKeeper.SetAllowlist(ctx, consumerID, providerAddr2)
	require.True(t, providerKeeper.IsAllowlisted(ctx, consumerID, providerAddr2))
	require.False(t, providerKeeper.IsAllowlistEmpty(ctx, consumerID))

	providerKeeper.DeleteAllowlist(ctx, consumerID)
	require.False(t, providerKeeper.IsAllowlisted(ctx, consumerID, providerAddr1))
	require.False(t, providerKeeper.IsAllowlisted(ctx, consumerID, providerAddr2))
	require.True(t, providerKeeper.IsAllowlistEmpty(ctx, consumerID))
}

func TestUpdateAllowlist(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	consumerId := "0"

	providerConsAddr1 := "cosmosvalcons1qmq08eruchr5sf5s3rwz7djpr5a25f7xw4mceq"
	consAddr1, _ := sdk.ConsAddressFromBech32(providerConsAddr1)
	providerConsAddr2 := "cosmosvalcons1nx7n5uh0ztxsynn4sje6eyq2ud6rc6klc96w39"
	consAddr2, _ := sdk.ConsAddressFromBech32(providerConsAddr2)

	providerKeeper.UpdateAllowlist(ctx, consumerId, []string{providerConsAddr1, providerConsAddr2})

	expectedAllowlist := []providertypes.ProviderConsAddress{
		providertypes.NewProviderConsAddress(consAddr1),
		providertypes.NewProviderConsAddress(consAddr2),
	}
	require.Equal(t, expectedAllowlist, providerKeeper.GetAllowList(ctx, consumerId))
}

// TestDenylist tests the `SetDenylist`, `IsDenylisted`, `DeleteDenylist`, and `IsDenylistEmpty` methods
func TestDenylist(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	consumerID := CONSUMER_ID

	// no validator was denylisted and hence the denylist is empty
	require.True(t, providerKeeper.IsDenylistEmpty(ctx, consumerID))

	providerAddr1 := providertypes.NewProviderConsAddress([]byte("providerAddr1"))
	providerKeeper.SetDenylist(ctx, consumerID, providerAddr1)
	require.True(t, providerKeeper.IsDenylisted(ctx, consumerID, providerAddr1))

	// denylist is not empty anymore
	require.False(t, providerKeeper.IsDenylistEmpty(ctx, consumerID))

	providerAddr2 := providertypes.NewProviderConsAddress([]byte("providerAddr2"))
	providerKeeper.SetDenylist(ctx, consumerID, providerAddr2)
	require.True(t, providerKeeper.IsDenylisted(ctx, consumerID, providerAddr2))
	require.False(t, providerKeeper.IsDenylistEmpty(ctx, consumerID))

	providerKeeper.DeleteDenylist(ctx, consumerID)
	require.False(t, providerKeeper.IsDenylisted(ctx, consumerID, providerAddr1))
	require.False(t, providerKeeper.IsDenylisted(ctx, consumerID, providerAddr2))
	require.True(t, providerKeeper.IsDenylistEmpty(ctx, consumerID))
}

func TestUpdateDenylist(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	consumerId := "0"

	providerConsAddr1 := "cosmosvalcons1qmq08eruchr5sf5s3rwz7djpr5a25f7xw4mceq"
	consAddr1, _ := sdk.ConsAddressFromBech32(providerConsAddr1)
	providerConsAddr2 := "cosmosvalcons1nx7n5uh0ztxsynn4sje6eyq2ud6rc6klc96w39"
	consAddr2, _ := sdk.ConsAddressFromBech32(providerConsAddr2)

	providerKeeper.UpdateDenylist(ctx, consumerId, []string{providerConsAddr1, providerConsAddr2})

	expectedDenylist := []providertypes.ProviderConsAddress{
		providertypes.NewProviderConsAddress(consAddr1),
		providertypes.NewProviderConsAddress(consAddr2),
	}
	require.Equal(t, expectedDenylist, providerKeeper.GetDenyList(ctx, consumerId))
}

// Tests setting, getting and deleting parameters that are stored per-consumer chain.
// The tests cover the following parameters:
// - MinimumPowerInTopN
func TestKeeperConsumerParams(t *testing.T) {
	k, ctx, _, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))

	tests := []struct {
		name         string
		settingFunc  func(sdk.Context, string, int64)
		getFunc      func(sdk.Context, string) int64
		deleteFunc   func(sdk.Context, string)
		initialValue int64
		updatedValue int64
	}{
		{
			name:        "Minimum Power In Top N",
			settingFunc: func(ctx sdk.Context, id string, val int64) { k.SetMinimumPowerInTopN(ctx, id, val) },
			getFunc: func(ctx sdk.Context, id string) int64 {
				minimumPowerInTopN, _ := k.GetMinimumPowerInTopN(ctx, id)
				return minimumPowerInTopN
			},
			deleteFunc:   func(ctx sdk.Context, id string) { k.DeleteMinimumPowerInTopN(ctx, id) },
			initialValue: 1000,
			updatedValue: 2000,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			consumerID := CONSUMER_ID
			// Set initial value
			tt.settingFunc(ctx, consumerID, tt.initialValue)

			// Retrieve and check initial value
			actualValue := tt.getFunc(ctx, consumerID)
			require.EqualValues(t, tt.initialValue, actualValue)

			// Update value
			tt.settingFunc(ctx, consumerID, tt.updatedValue)

			// Retrieve and check updated value
			newActualValue := tt.getFunc(ctx, consumerID)
			require.EqualValues(t, tt.updatedValue, newActualValue)

			// Check non-existent consumer id
			res := tt.getFunc(ctx, "not the consumerId")
			require.Zero(t, res)

			// Delete value
			tt.deleteFunc(ctx, consumerID)

			// Check that value was deleted
			res = tt.getFunc(ctx, consumerID)
			require.Zero(t, res)

			// Try deleting again
			tt.deleteFunc(ctx, consumerID)

			// Check that the value is still deleted
			res = tt.getFunc(ctx, consumerID)
			require.Zero(t, res)
		})
	}
}

func TestUpdateMinimumPowerInTopN(t *testing.T) {
	providerKeeper, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	consumerId := "0"

	// test case where Top N is 0 in which case there's no minimum power in top N
	err := providerKeeper.SetConsumerPowerShapingParameters(ctx, consumerId, providertypes.PowerShapingParameters{
		Top_N: 0,
	})
	require.NoError(t, err)

	err = providerKeeper.UpdateMinimumPowerInTopN(ctx, consumerId, 0, 0)
	require.NoError(t, err)
	_, found := providerKeeper.GetMinimumPowerInTopN(ctx, consumerId)
	require.False(t, found)

	// test cases where Top N > 0 and for this we mock some validators
	powers := []int64{10, 20, 30}
	validators := []stakingtypes.Validator{
		createStakingValidator(ctx, mocks, powers[0], 1), // this validator has ~16 of the total voting power
		createStakingValidator(ctx, mocks, powers[1], 2), // this validator has ~33% of the total voting gpower
		createStakingValidator(ctx, mocks, powers[2], 3), // this validator has 50% of the total voting power
	}
	mocks.MockStakingKeeper.EXPECT().GetBondedValidatorsByPower(gomock.Any()).Return(validators, nil).AnyTimes()

	maxProviderConsensusValidators := int64(3)
	params := providerKeeper.GetParams(ctx)
	params.MaxProviderConsensusValidators = maxProviderConsensusValidators
	providerKeeper.SetParams(ctx, params)

	// when top N is 50, the minimum power is 30 (because top validator has to validate)
	err = providerKeeper.SetConsumerPowerShapingParameters(ctx, consumerId, providertypes.PowerShapingParameters{
		Top_N: 50,
	})
	require.NoError(t, err)
	err = providerKeeper.UpdateMinimumPowerInTopN(ctx, consumerId, 0, 50)
	require.NoError(t, err)
	minimumPowerInTopN, found := providerKeeper.GetMinimumPowerInTopN(ctx, consumerId)
	require.True(t, found)
	require.Equal(t, int64(30), minimumPowerInTopN)

	// when top N is 51, the minimum power is 20 (because top 2 validators have to validate)
	err = providerKeeper.SetConsumerPowerShapingParameters(ctx, consumerId, providertypes.PowerShapingParameters{
		Top_N: 51,
	})
	require.NoError(t, err)
	err = providerKeeper.UpdateMinimumPowerInTopN(ctx, consumerId, 50, 51)
	require.NoError(t, err)
	minimumPowerInTopN, found = providerKeeper.GetMinimumPowerInTopN(ctx, consumerId)
	require.True(t, found)
	require.Equal(t, int64(20), minimumPowerInTopN)

	// when top N is 100, the minimum power is 10 (that of the validator with the lowest power)
	err = providerKeeper.SetConsumerPowerShapingParameters(ctx, consumerId, providertypes.PowerShapingParameters{
		Top_N: 100,
	})
	require.NoError(t, err)
	err = providerKeeper.UpdateMinimumPowerInTopN(ctx, consumerId, 51, 100)
	require.NoError(t, err)
	minimumPowerInTopN, found = providerKeeper.GetMinimumPowerInTopN(ctx, consumerId)
	require.True(t, found)
	require.Equal(t, int64(10), minimumPowerInTopN)
}

func TestPrioritylist(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	consumerID := CONSUMER_ID

	// no validator was prioritylisted and hence the prioritylist is empty
	require.True(t, providerKeeper.IsPrioritylistEmpty(ctx, consumerID))

	providerAddr1 := providertypes.NewProviderConsAddress([]byte("providerAddr1"))
	providerKeeper.SetPrioritylist(ctx, consumerID, providerAddr1)
	require.True(t, providerKeeper.IsPrioritylisted(ctx, consumerID, providerAddr1))

	// prioritylist is not empty anymore
	require.False(t, providerKeeper.IsPrioritylistEmpty(ctx, consumerID))

	providerAddr2 := providertypes.NewProviderConsAddress([]byte("providerAddr2"))
	providerKeeper.SetPrioritylist(ctx, consumerID, providerAddr2)
	require.True(t, providerKeeper.IsPrioritylisted(ctx, consumerID, providerAddr2))
	require.False(t, providerKeeper.IsPrioritylistEmpty(ctx, consumerID))

	providerKeeper.DeletePrioritylist(ctx, consumerID)
	require.False(t, providerKeeper.IsPrioritylisted(ctx, consumerID, providerAddr1))
	require.False(t, providerKeeper.IsPrioritylisted(ctx, consumerID, providerAddr2))
	require.True(t, providerKeeper.IsPrioritylistEmpty(ctx, consumerID))
}

func TestUpdatePrioritylist(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	consumerId := "0"

	providerConsAddr1 := "cosmosvalcons1qmq08eruchr5sf5s3rwz7djpr5a25f7xw4mceq"
	consAddr1, _ := sdk.ConsAddressFromBech32(providerConsAddr1)
	providerConsAddr2 := "cosmosvalcons1nx7n5uh0ztxsynn4sje6eyq2ud6rc6klc96w39"
	consAddr2, _ := sdk.ConsAddressFromBech32(providerConsAddr2)

	providerKeeper.UpdatePrioritylist(ctx, consumerId, []string{providerConsAddr1, providerConsAddr2})

	expectedPrioritylist := []providertypes.ProviderConsAddress{
		providertypes.NewProviderConsAddress(consAddr1),
		providertypes.NewProviderConsAddress(consAddr2),
	}
	require.Equal(t, expectedPrioritylist, providerKeeper.GetPriorityList(ctx, consumerId))
}
