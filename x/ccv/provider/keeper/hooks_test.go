package keeper_test

import (
	"testing"

	"github.com/golang/mock/gomock"

	sdk "github.com/cosmos/cosmos-sdk/types"

	providerkeeper "github.com/cosmos/interchain-security/v3/x/ccv/provider/keeper"
	ututil "github.com/cosmos/interchain-security/v3/x/ccv/types/unit_test_util"
)

func TestValidatorConsensusKeyInUse(t *testing.T) {
	newValidator := ututil.NewCryptoIdentityFromIntSeed(0)
	anotherValidator0 := ututil.NewCryptoIdentityFromIntSeed(1)
	anotherValidator1 := ututil.NewCryptoIdentityFromIntSeed(2)

	tests := []struct {
		name   string
		setup  func(sdk.Context, providerkeeper.Keeper)
		expect bool
	}{
		{
			name: "not in use by another validator",
			setup: func(ctx sdk.Context, k providerkeeper.Keeper) {
				// Another validator does not exist
			},
			expect: false,
		},
		{
			name: "in use by another validator",
			setup: func(ctx sdk.Context, k providerkeeper.Keeper) {
				// We are trying to add a new validator, but its address has already been used
				// by another validator
				k.SetValidatorByConsumerAddr(ctx, "chainid",
					newValidator.ConsumerConsAddress(),
					anotherValidator0.ProviderConsAddress(),
				)
			},
			expect: true,
		},
		{
			name: "in use by one of several other validators",
			setup: func(ctx sdk.Context, k providerkeeper.Keeper) {
				// We are trying to add a new validator, but its address has already been used
				// by another validator, of which there are several, across potentially several chains
				k.SetValidatorByConsumerAddr(ctx, "chainid0",
					newValidator.ConsumerConsAddress(),
					anotherValidator0.ProviderConsAddress(),
				)
				k.SetValidatorByConsumerAddr(ctx, "chainid1",
					anotherValidator1.ConsumerConsAddress(),
					anotherValidator1.ProviderConsAddress(),
				)
			},
			expect: true,
		},
	}
	for _, tt := range tests {
		k, ctx, _, mocks := ututil.GetProviderKeeperAndCtx(t, ututil.NewInMemKeeperParams(t))

		gomock.InOrder(
			mocks.MockStakingKeeper.EXPECT().GetValidator(ctx,
				newValidator.SDKValOpAddress(),
			).Return(newValidator.SDKStakingValidator(), true),
		)

		tt.setup(ctx, k)

		t.Run(tt.name, func(t *testing.T) {
			if actual := providerkeeper.ValidatorConsensusKeyInUse(&k, ctx, newValidator.SDKStakingValidator().GetOperator()); actual != tt.expect {
				t.Errorf("validatorConsensusKeyInUse() = %v, want %v", actual, tt.expect)
			}
		})
	}
}
