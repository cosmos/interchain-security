package keeper_test

import (
	"fmt"
	"testing"
	"time"

	authtypes "github.com/cosmos/cosmos-sdk/x/auth/types"
	clienttypes "github.com/cosmos/ibc-go/v7/modules/core/02-client/types"
	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"

	sdk "github.com/cosmos/cosmos-sdk/types"
	v1 "github.com/cosmos/cosmos-sdk/x/gov/types/v1"

	cryptotestutil "github.com/cosmos/interchain-security/v3/testutil/crypto"
	testkeeper "github.com/cosmos/interchain-security/v3/testutil/keeper"
	providerkeeper "github.com/cosmos/interchain-security/v3/x/ccv/provider/keeper"
	"github.com/cosmos/interchain-security/v3/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/v3/x/ccv/types"
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
				// We are trying to add a new validator, but its address has already been used
				// by another validator
				k.SetValidatorByConsumerAddr(ctx, "chainid",
					newValidator.ConsumerConsAddress(),
					anotherValidator0.ProviderConsAddress(),
				)
				k.SetConsumerClientId(ctx, "chainid", "clientID")
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
				k.SetConsumerClientId(ctx, "chainid0", "clientID0")

				k.SetValidatorByConsumerAddr(ctx, "chainid1",
					anotherValidator1.ConsumerConsAddress(),
					anotherValidator1.ProviderConsAddress(),
				)
				k.SetConsumerClientId(ctx, "chainid1", "clientID1")
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

func TestAfterProposalSubmission(t *testing.T) {
	// encodingConfig := appparams.MakeTestEncodingConfig()
	// v1beta1.RegisterInterfaces(encodingConfig.InterfaceRegistry)
	// v1.RegisterInterfaces(encodingConfig.InterfaceRegistry)
	// cdc := encodingConfig.Codec

	k, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	newValidator := cryptotestutil.NewCryptoIdentityFromIntSeed(0)

	content := types.NewConsumerAdditionProposal(
		"chainID",
		"description",
		"chainID",
		clienttypes.NewHeight(4, 5),
		[]byte("gen_hash"),
		[]byte("bin_hash"),
		time.Now(),
		ccvtypes.DefaultConsumerRedistributeFrac,
		ccvtypes.DefaultBlocksPerDistributionTransmission,
		"",
		ccvtypes.DefaultHistoricalEntries,
		ccvtypes.DefaultCCVTimeoutPeriod,
		ccvtypes.DefaultTransferTimeoutPeriod,
		ccvtypes.DefaultConsumerUnbondingPeriod,
	)

	propContent, err := v1.NewLegacyContent(content, authtypes.NewModuleAddress("gov").String())
	require.NoError(t, err)

	// _, err = v1.LegacyContentFromMessage(propContent)
	// require.NoError(t, err)

	prop, err := v1.NewProposal(
		[]sdk.Msg{propContent},
		0,
		time.Now(),
		time.Now(),
		"",
		"",
		"",
		// sdk.NewCoins(sdk.NewCoin("stake", math.OneInt())),
		sdk.AccAddress(newValidator.SDKValOpAddress()),
	)

	require.NoError(t, err)

	gomock.InOrder(
		mocks.MockGovKeeper.EXPECT().GetProposal(ctx, uint64(0)).Return(prop, true),
	)

	tHooks := k.Hooks()
	tHooks.AfterProposalSubmission(ctx, 0)

	fmt.Println(len(k.GetAllProposedConsumerChainIDs(ctx)))
}
