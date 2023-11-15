package keeper_test

import (
	"testing"
	"time"

	"github.com/golang/mock/gomock"
	"github.com/stretchr/testify/require"

	"cosmossdk.io/math"

	sdk "github.com/cosmos/cosmos-sdk/types"
	authtypes "github.com/cosmos/cosmos-sdk/x/auth/types"
	banktypes "github.com/cosmos/cosmos-sdk/x/bank/types"
	v1 "github.com/cosmos/cosmos-sdk/x/gov/types/v1"
	"github.com/cosmos/cosmos-sdk/x/gov/types/v1beta1"

	cryptotestutil "github.com/cosmos/interchain-security/v3/testutil/crypto"
	testkeeper "github.com/cosmos/interchain-security/v3/testutil/keeper"
	providerkeeper "github.com/cosmos/interchain-security/v3/x/ccv/provider/keeper"
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

func TestAfterPropSubmissionAndVotingPeriodEnded(t *testing.T) {
	acct := cryptotestutil.NewCryptoIdentityFromIntSeed(0)

	propMsg, err := v1.NewLegacyContent(
		testkeeper.GetTestConsumerAdditionProp(),
		authtypes.NewModuleAddress("gov").String(),
	)
	require.NoError(t, err)

	prop, err := v1.NewProposal(
		[]sdk.Msg{propMsg},
		0,
		time.Now(),
		time.Now(),
		"",
		"",
		"",
		sdk.AccAddress(acct.SDKValOpAddress()),
	)
	require.NoError(t, err)

	k, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	// pass the prop to the mocked gov keeper,
	// which is called by both the AfterProposalVotingPeriodEnded and
	// AfterProposalSubmission gov hooks
	gomock.InOrder(
		mocks.MockGovKeeper.EXPECT().GetProposal(ctx, prop.Id).Return(prop, true).Times(2),
	)

	k.Hooks().AfterProposalSubmission(ctx, prop.Id)
	// verify that the proposal ID is created
	require.NotEmpty(t, k.GetProposedConsumerChain(ctx, prop.Id))

	k.Hooks().AfterProposalVotingPeriodEnded(ctx, prop.Id)
	// verify that the proposal ID is deleted
	require.Empty(t, k.GetProposedConsumerChain(ctx, prop.Id))
}

func TestGetConsumerAdditionLegacyPropFromProp(t *testing.T) {
	acct := cryptotestutil.NewCryptoIdentityFromIntSeed(0)
	anotherAcct := cryptotestutil.NewCryptoIdentityFromIntSeed(1)

	// create a dummy bank send message
	dummyMsg := &banktypes.MsgSend{
		FromAddress: sdk.AccAddress(acct.SDKValOpAddress()).String(),
		ToAddress:   sdk.AccAddress(anotherAcct.SDKValOpAddress()).String(),
		Amount:      sdk.NewCoins(sdk.NewCoin("stake", math.OneInt())),
	}

	textProp, err := v1.NewLegacyContent(
		v1beta1.NewTextProposal("a title", "a legacy text prop"),
		authtypes.NewModuleAddress("gov").String(),
	)
	require.NoError(t, err)

	consuProp, err := v1.NewLegacyContent(
		testkeeper.GetTestConsumerAdditionProp(),
		authtypes.NewModuleAddress("gov").String(),
	)
	require.NoError(t, err)

	testCases := map[string]struct {
		propMsg sdk.Msg
		// setup 			func(sdk.Context, k providerkeeper, proposalID uint64)
		expPanic        bool
		expConsuAddProp bool
	}{
		"prop not found": {
			propMsg:  nil,
			expPanic: true,
		},
		"msgs in prop contain no legacy props": {
			propMsg: dummyMsg,
		},
		"msgs contain a legacy prop but not of ConsumerAdditionProposal type": {
			propMsg: textProp,
		},
		"msgs contain an invalid legacy prop": {
			propMsg:  &v1.MsgExecLegacyContent{},
			expPanic: true,
		},
		"msg contains a prop of ConsumerAdditionProposal type - hook should create a new proposed chain": {
			propMsg:         consuProp,
			expConsuAddProp: true,
		},
	}

	for name, tc := range testCases {
		t.Run(name, func(t *testing.T) {
			k, ctx, ctrl, mocks := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
			defer ctrl.Finish()

			var (
				prop      v1.Proposal
				propFound bool
			)

			if tc.propMsg != nil {
				propFound = true
				prop, err = v1.NewProposal(
					[]sdk.Msg{tc.propMsg},
					0,
					time.Now(),
					time.Now(),
					"",
					"",
					"",
					sdk.AccAddress(acct.SDKValOpAddress()),
				)
				require.NoError(t, err)
			}

			gomock.InOrder(
				mocks.MockGovKeeper.EXPECT().GetProposal(ctx, prop.Id).Return(prop, propFound),
			)

			if tc.expPanic {
				defer func() {
					// fail test if not panic was recovered
					if r := recover(); r == nil {
						require.Fail(t, r.(string))
					}
				}()
			}

			// retrieve consumer addition proposal
			_, ok := k.Hooks().GetConsumerAdditionLegacyPropFromProp(ctx, prop.Id)
			require.Equal(t, tc.expConsuAddProp, ok)
		})
	}
}
