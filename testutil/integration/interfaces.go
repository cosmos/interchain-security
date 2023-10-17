package integration

import (
	"context"
	"time"

	ibctesting "github.com/cosmos/ibc-go/v8/testing"

	"cosmossdk.io/math"

	"cosmossdk.io/core/comet"

	evidencetypes "cosmossdk.io/x/evidence/types"
	cryptotypes "github.com/cosmos/cosmos-sdk/crypto/types"
	sdk "github.com/cosmos/cosmos-sdk/types"
	authtypes "github.com/cosmos/cosmos-sdk/x/auth/types"
	distributiontypes "github.com/cosmos/cosmos-sdk/x/distribution/types"
	govv1 "github.com/cosmos/cosmos-sdk/x/gov/types/v1"
	minttypes "github.com/cosmos/cosmos-sdk/x/mint/types"
	paramstypes "github.com/cosmos/cosmos-sdk/x/params/types"
	slashingtypes "github.com/cosmos/cosmos-sdk/x/slashing/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	consumerkeeper "github.com/cosmos/interchain-security/v3/x/ccv/consumer/keeper"
	providerkeeper "github.com/cosmos/interchain-security/v3/x/ccv/provider/keeper"
	ccvtypes "github.com/cosmos/interchain-security/v3/x/ccv/types"
)

// The interface that any provider app must implement to be compatible with ccv integration tests.
// This is a wrapper around the ibc testing app interface with additional constraints.
type ProviderApp interface {
	ibctesting.TestingApp
	GetSubspace(moduleName string) paramstypes.Subspace

	//
	// Keeper getters
	//

	GetProviderKeeper() providerkeeper.Keeper
	// Returns a staking keeper interface with more capabilities than the expected_keepers interface
	GetTestStakingKeeper() TestStakingKeeper
	// Returns a bank keeper interface with more capabilities than the expected_keepers interface
	GetTestBankKeeper() TestBankKeeper
	// Returns a slashing keeper interface with more capabilities than the expected_keepers interface
	GetTestSlashingKeeper() TestSlashingKeeper
	// Returns a distribution keeper interface with more capabilities than the expected_keepers interface
	GetTestDistributionKeeper() TestDistributionKeeper
	// Returns an account keeper interface with more capabilities than the expected_keepers interface
	GetTestAccountKeeper() TestAccountKeeper
}

// The interface that any consumer app must implement to be compatible with integration tests
// This is a wrapper around the ibc testing app interface with additional constraints.
type ConsumerApp interface {
	ibctesting.TestingApp

	// BeginBlocker(ctx sdk.Context, req abci.RequestBeginBlock) abci.ResponseBeginBlock
	GetConsumerKeeper() consumerkeeper.Keeper
	GetSubspace(moduleName string) paramstypes.Subspace

	//
	// Keeper getters
	//

	// Returns a bank keeper interface with more capabilities than the expected_keepers interface
	GetTestBankKeeper() TestBankKeeper
	// Tests an account keeper interface with more capabilities than the expected_keepers interface
	GetTestAccountKeeper() TestAccountKeeper
	// Tests a slashing keeper interface with more capabilities than the expected_keepers interface
	GetTestSlashingKeeper() TestSlashingKeeper
	// Tests an evidence keeper interface with more capabilities than the expected_keepers interface
	GetTestEvidenceKeeper() TestEvidenceKeeper
}

type DemocConsumerApp interface {
	ConsumerApp
	// Returns a distribution keeper interface with more capabilities than the expected_keepers interface
	GetTestDistributionKeeper() TestDistributionKeeper
	// Tests a staking keeper interface with more capabilities than the expected_keepers interface
	GetTestStakingKeeper() TestStakingKeeper
	// Tests a mint keeper interface with more capabilities than the expected_keepers interface
	GetTestMintKeeper() TestMintKeeper
	// Tests a gov keeper interface with more capabilities than the expected_keepers interface
	GetTestGovKeeper() TestGovKeeper
}

//
// The following keeper interfaces are wrappers around the expected keepers for ccv modules,
// since integration tests require extra functionality from external keepers.
//

// NOTE: @MSalopek this is a bit confusing to me
// See if this needs a bigger refactor
type TestStakingKeeper interface {
	ccvtypes.StakingKeeper
	Delegate(
		ctx context.Context, delAddr sdk.AccAddress, bondAmt math.Int, tokenSrc stakingtypes.BondStatus,
		validator stakingtypes.Validator, subtractAccount bool,
	) (newShares math.LegacyDec, err error)
	Undelegate(ctx context.Context, delAddr sdk.AccAddress, valAddr sdk.ValAddress, sharesAmount math.LegacyDec,
	) (time.Time, math.Int, error)
	BeginRedelegation(
		ctx context.Context, delAddr sdk.AccAddress, valSrcAddr, valDstAddr sdk.ValAddress, sharesAmount math.LegacyDec,
	) (completionTime time.Time, err error)
	GetUnbondingDelegationByUnbondingID(ctx context.Context, id uint64) (ubd stakingtypes.UnbondingDelegation, err error)
	GetRedelegations(ctx context.Context, delegator sdk.AccAddress, maxRetrieve uint16) (redelegations []stakingtypes.Redelegation, err error)
	GetUnbondingDelegation(ctx context.Context, delAddr sdk.AccAddress, valAddr sdk.ValAddress) (ubd stakingtypes.UnbondingDelegation, err error)
	GetAllValidators(ctx context.Context) (validators []stakingtypes.Validator, err error)
	GetValidatorSet() stakingtypes.ValidatorSet
}

type TestBankKeeper interface {
	ccvtypes.BankKeeper
	SendCoinsFromAccountToModule(ctx context.Context, senderAddr sdk.AccAddress,
		recipientModule string, amt sdk.Coins) error
	SendCoinsFromModuleToAccount(ctx context.Context, senderModule string,
		recipientAddr sdk.AccAddress, amt sdk.Coins) error
}

type TestAccountKeeper interface {
	ccvtypes.AccountKeeper
	GetParams(context.Context) authtypes.Params
}

type TestSlashingKeeper interface {
	ccvtypes.SlashingKeeper
	IterateMissedBlockBitmap(ctx context.Context, addr sdk.ConsAddress, cb func(index int64, missed bool) (stop bool)) error
	SetValidatorSigningInfo(ctx context.Context, address sdk.ConsAddress, info slashingtypes.ValidatorSigningInfo) error
	SignedBlocksWindow(ctx context.Context) (int64, error)
	HandleValidatorSignature(ctx context.Context, addr cryptotypes.Address, power int64, signed comet.BlockIDFlag) error
	MinSignedPerWindow(ctx context.Context) (int64, error)
	// NOTE: @MSalopek deprecated in v50
	// IterateValidatorMissedBlockBitArray(ctx sdk.Context,
	// address sdk.ConsAddress, handler func(index int64, missed bool) (stop bool))
}

type TestEvidenceKeeper interface {
	HandleEquivocationEvidence(ctx sdk.Context, evidence *evidencetypes.Equivocation)
}

type TestDistributionKeeper interface {
	// NOTE: @MSalopek deprecated in v50
	// GetFeePoolCommunityCoins(ctx sdk.Context) sdk.DecCoins
	GetDistributionAccount(ctx context.Context) sdk.ModuleAccountI
	GetValidatorOutstandingRewards(ctx context.Context, val sdk.ValAddress) (rewards distributiontypes.ValidatorOutstandingRewards, err error)
	GetCommunityTax(ctx context.Context) (math.LegacyDec, error)
}

type TestMintKeeper interface {
	GetParams(ctx sdk.Context) (params minttypes.Params)
}

type TestGovKeeper interface {
	GetParams(ctx sdk.Context) govv1.Params
	SetParams(ctx sdk.Context, params govv1.Params) error
	SubmitProposal(ctx sdk.Context, messages []sdk.Msg, metadata, title, summary string, proposer sdk.AccAddress) (govv1.Proposal, error)
	AddDeposit(ctx sdk.Context, proposalID uint64, depositorAddr sdk.AccAddress, depositAmount sdk.Coins) (bool, error)
	AddVote(ctx sdk.Context, proposalID uint64, voterAddr sdk.AccAddress, options govv1.WeightedVoteOptions, metadata string) error
}
