package integration

import (
	"time"

	"cosmossdk.io/math"
	abci "github.com/cometbft/cometbft/abci/types"
	cryptotypes "github.com/cosmos/cosmos-sdk/crypto/types"
	sdk "github.com/cosmos/cosmos-sdk/types"
	authtypes "github.com/cosmos/cosmos-sdk/x/auth/types"
	distributiontypes "github.com/cosmos/cosmos-sdk/x/distribution/types"
	evidencetypes "github.com/cosmos/cosmos-sdk/x/evidence/types"
	govv1 "github.com/cosmos/cosmos-sdk/x/gov/types/v1"
	minttypes "github.com/cosmos/cosmos-sdk/x/mint/types"
	paramstypes "github.com/cosmos/cosmos-sdk/x/params/types"
	slashingtypes "github.com/cosmos/cosmos-sdk/x/slashing/types"
	"github.com/cosmos/cosmos-sdk/x/staking/types"

	ibctesting "github.com/cosmos/interchain-security/v2/legacy_ibc_testing/testing"
	consumerkeeper "github.com/cosmos/interchain-security/v2/x/ccv/consumer/keeper"
	providerkeeper "github.com/cosmos/interchain-security/v2/x/ccv/provider/keeper"
	ccvtypes "github.com/cosmos/interchain-security/v2/x/ccv/types"
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

	BeginBlocker(ctx sdk.Context, req abci.RequestBeginBlock) abci.ResponseBeginBlock
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

type TestStakingKeeper interface {
	ccvtypes.StakingKeeper
	Delegate(ctx sdk.Context, delAddr sdk.AccAddress, bondAmt math.Int, tokenSrc types.BondStatus,
		validator types.Validator, subtractAccount bool) (newShares sdk.Dec, err error)
	Undelegate(ctx sdk.Context, delAddr sdk.AccAddress, valAddr sdk.ValAddress, sharesAmount sdk.Dec,
	) (time.Time, error)
	BeginRedelegation(ctx sdk.Context, delAddr sdk.AccAddress, valSrcAddr, valDstAddr sdk.ValAddress,
		sharesAmount sdk.Dec) (completionTime time.Time, err error)
	GetUnbondingDelegationByUnbondingID(ctx sdk.Context, id uint64,
	) (ubd types.UnbondingDelegation, found bool)
	GetRedelegations(ctx sdk.Context, delegator sdk.AccAddress,
		maxRetrieve uint16) (redelegations []types.Redelegation)
	BondDenom(ctx sdk.Context) (res string)
	IsValidatorJailed(ctx sdk.Context, addr sdk.ConsAddress) bool
	GetUnbondingDelegation(ctx sdk.Context, delAddr sdk.AccAddress, valAddr sdk.ValAddress,
	) (ubd types.UnbondingDelegation, found bool)
	GetAllValidators(ctx sdk.Context) (validators []types.Validator)
	GetValidatorSet() types.ValidatorSet
}

type TestBankKeeper interface {
	ccvtypes.BankKeeper
	SendCoinsFromAccountToModule(ctx sdk.Context, senderAddr sdk.AccAddress,
		recipientModule string, amt sdk.Coins) error
	SendCoinsFromModuleToAccount(ctx sdk.Context, senderModule string,
		recipientAddr sdk.AccAddress, amt sdk.Coins) error
}

type TestAccountKeeper interface {
	ccvtypes.AccountKeeper
	GetParams(sdk.Context) authtypes.Params
}

type TestSlashingKeeper interface {
	ccvtypes.SlashingKeeper
	SetValidatorSigningInfo(ctx sdk.Context, address sdk.ConsAddress,
		info slashingtypes.ValidatorSigningInfo)
	SignedBlocksWindow(ctx sdk.Context) (res int64)
	HandleValidatorSignature(ctx sdk.Context, addr cryptotypes.Address, power int64, signed bool)
	MinSignedPerWindow(ctx sdk.Context) int64
	IterateValidatorMissedBlockBitArray(ctx sdk.Context,
		address sdk.ConsAddress, handler func(index int64, missed bool) (stop bool))
}

type TestEvidenceKeeper interface {
	HandleEquivocationEvidence(ctx sdk.Context, evidence *evidencetypes.Equivocation)
}

type TestDistributionKeeper interface {
	GetFeePoolCommunityCoins(ctx sdk.Context) sdk.DecCoins
	GetDistributionAccount(ctx sdk.Context) authtypes.ModuleAccountI
	GetValidatorOutstandingRewards(ctx sdk.Context,
		val sdk.ValAddress) (rewards distributiontypes.ValidatorOutstandingRewards)
	GetCommunityTax(ctx sdk.Context) (percent sdk.Dec)
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
