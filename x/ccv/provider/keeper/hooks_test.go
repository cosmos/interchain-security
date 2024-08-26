package keeper_test

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	cryptotestutil "github.com/cosmos/interchain-security/v5/testutil/crypto"
	testkeeper "github.com/cosmos/interchain-security/v5/testutil/keeper"
	providerkeeper "github.com/cosmos/interchain-security/v5/x/ccv/provider/keeper"
	"github.com/golang/mock/gomock"
	"testing"
)

func TestValidatorConsensusKeyInUse(t *testing.T) {
	newValidator := cryptotestutil.NewCryptoIdentityFromIntSeed(0)
	anotherValidator0 := cryptotestutil.NewCryptoIdentityFromIntSeed(1)
	anotherValidator1 := cryptotestutil.NewCryptoIdentityFromIntSeed(2)

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
				k.FetchAndIncrementConsumerId(ctx)
				k.SetConsumerPhase(ctx, "0", providerkeeper.Initialized)

				// We are trying to add a new validator, but its address has already been used
				// by another validator
				k.SetValidatorByConsumerAddr(ctx, "0",
					newValidator.ConsumerConsAddress(),
					anotherValidator0.ProviderConsAddress(),
				)
				k.SetConsumerClientId(ctx, "0", "clientId")
			},
			expect: true,
		},
		{
			name: "in use by one of several other validators",
			setup: func(ctx sdk.Context, k providerkeeper.Keeper) {
				k.FetchAndIncrementConsumerId(ctx)
				k.FetchAndIncrementConsumerId(ctx)
				k.SetConsumerPhase(ctx, "0", providerkeeper.Initialized)
				k.SetConsumerPhase(ctx, "1", providerkeeper.Initialized)

				// We are trying to add a new validator, but its address has already been used
				// by another validator, of which there are several, across potentially several chains
				k.SetValidatorByConsumerAddr(ctx, "0",
					newValidator.ConsumerConsAddress(),
					anotherValidator0.ProviderConsAddress(),
				)
				k.SetConsumerClientId(ctx, "0", "clientId0")

				k.SetValidatorByConsumerAddr(ctx, "1",
					anotherValidator1.ConsumerConsAddress(),
					anotherValidator1.ProviderConsAddress(),
				)
				k.SetConsumerClientId(ctx, "1", "clientId1")
			},
			expect: true,
		},
	}
	for _, tt := range tests {
		k, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
		defer ctrl.Finish()

		gomock.InOrder(
			mocks.MockStakingKeeper.EXPECT().GetValidator(ctx,
				newValidator.SDKValOpAddress(),
			).Return(newValidator.SDKStakingValidator(), nil),
		)

		tt.setup(ctx, k)

		t.Run(tt.name, func(t *testing.T) {
			if actual := k.ValidatorConsensusKeyInUse(ctx, newValidator.SDKValOpAddress()); actual != tt.expect {
				t.Errorf("validatorConsensusKeyInUse() = %v, want %v", actual, tt.expect)
			}
		})
	}
}
