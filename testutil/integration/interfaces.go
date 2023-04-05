package integration

import (
	"time"

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
	ibctesting "github.com/cosmos/interchain-security/legacy_ibc_testing/testing"
	consumerkeeper "github.com/cosmos/interchain-security/x/ccv/consumer/keeper"
	providerkeeper "github.com/cosmos/interchain-security/x/ccv/provider/keeper"
	ccvtypes "github.com/cosmos/interchain-security/x/ccv/types"
)

// The interface that any provider app must implement to be compatible with ccv integration tests.
// This is a wrapper around the ibc testing app interface with additional constraints.
type ProviderApp interface {
	ibctesting.AppTest

	//
	// Keeper getters
	//

	GetProviderKeeper() providerkeeper.Keeper
	// Returns a staking keeper interface with more capabilities than the expected_keepers interface
<<<<<<< HEAD:testutil/e2e/interfaces.go
	GetE2eStakingKeeper() StakingKeeper
	// Returns a bank keeper interface with more capabilities than the expected_keepers interface
	GetE2eBankKeeper() BankKeeper
	// Returns a slashing keeper interface with more capabilities than the expected_keepers interface
	GetE2eSlashingKeeper() SlashingKeeper
	// Returns a distribution keeper interface with more capabilities than the expected_keepers interface
	GetE2eDistributionKeeper() DistributionKeeper
=======
	GetTestStakingKeeper() TestStakingKeeper
	// Testurns a bank keeper interface with more capabilities than the expected_keepers interface
	GetTestBankKeeper() TestBankKeeper
	// Testurns a slashing keeper interface with more capabilities than the expected_keepers interface
	GetTestSlashingKeeper() TestSlashingKeeper
	// Integrurns a distribution keeper interface with more capabilities than the expected_keepers interface
	GetTestDistributionKeeper() TestDistributionKeeper
>>>>>>> main:testutil/integration/interfaces.go
}

// The interface that any consumer app must implement to be compatible with integration tests
// This is a wrapper around the ibc testing app interface with additional constraints.
type ConsumerApp interface {
	ibctesting.AppTest

	BeginBlocker(ctx sdk.Context, req abci.RequestBeginBlock) abci.ResponseBeginBlock
	GetConsumerKeeper() consumerkeeper.Keeper
	GetSubspace(moduleName string) paramstypes.Subspace

	//
	// Keeper getters
	//

	// Returns a bank keeper interface with more capabilities than the expected_keepers interface
<<<<<<< HEAD:testutil/e2e/interfaces.go
	GetE2eBankKeeper() BankKeeper
	// Returns an account keeper interface with more capabilities than the expected_keepers interface
	GetE2eAccountKeeper() AccountKeeper
	// Returns a slashing keeper interface with more capabilities than the expected_keepers interface
	GetE2eSlashingKeeper() SlashingKeeper
	// Returns an evidence keeper interface with more capabilities than the expected_keepers interface
	GetE2eEvidenceKeeper() EvidenceKeeper
=======
	GetTestBankKeeper() TestBankKeeper
	// Tests an account keeper interface with more capabilities than the expected_keepers interface
	GetTestAccountKeeper() TestAccountKeeper
	// Tests a slashing keeper interface with more capabilities than the expected_keepers interface
	GetTestSlashingKeeper() TestSlashingKeeper
	// Tests an evidence keeper interface with more capabilities than the expected_keepers interface
	GetTestEvidenceKeeper() TestEvidenceKeeper
>>>>>>> main:testutil/integration/interfaces.go
}

type DemocConsumerApp interface {
	ConsumerApp
	// Returns a distribution keeper interface with more capabilities than the expected_keepers interface
<<<<<<< HEAD:testutil/e2e/interfaces.go
	GetE2eDistributionKeeper() DistributionKeeper
	// Returns a staking keeper interface with more capabilities than the expected_keepers interface
	GetE2eStakingKeeper() StakingKeeper
	// Returns a mint keeper interface with more capabilities than the expected_keepers interface
	GetE2eMintKeeper() MintKeeper
	// Returns a gov keeper interface with more capabilities than the expected_keepers interface
	GetE2eGovKeeper() GovKeeper
=======
	GetTestDistributionKeeper() TestDistributionKeeper
	// Tests a staking keeper interface with more capabilities than the expected_keepers interface
	GetTestStakingKeeper() TestStakingKeeper
	// Tests a mint keeper interface with more capabilities than the expected_keepers interface
	GetTestMintKeeper() TestMintKeeper
	// Tests a gov keeper interface with more capabilities than the expected_keepers interface
	GetTestGovKeeper() TestGovKeeper
>>>>>>> main:testutil/integration/interfaces.go
}

//
// The following keeper interfaces are wrappers around the expected keepers for ccv modules,
// since integration tests require extra functionality from external keepers.
//

<<<<<<< HEAD:testutil/e2e/interfaces.go
type StakingKeeper interface {
=======
type TestStakingKeeper interface {
>>>>>>> main:testutil/integration/interfaces.go
	ccvtypes.StakingKeeper
	Delegate(ctx sdk.Context, delAddr sdk.AccAddress, bondAmt sdk.Int, tokenSrc types.BondStatus,
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

<<<<<<< HEAD:testutil/e2e/interfaces.go
type BankKeeper interface {
=======
type TestBankKeeper interface {
>>>>>>> main:testutil/integration/interfaces.go
	ccvtypes.BankKeeper
	SendCoinsFromAccountToModule(ctx sdk.Context, senderAddr sdk.AccAddress,
		recipientModule string, amt sdk.Coins) error
}

<<<<<<< HEAD:testutil/e2e/interfaces.go
type AccountKeeper interface {
=======
type TestAccountKeeper interface {
>>>>>>> main:testutil/integration/interfaces.go
	ccvtypes.AccountKeeper
	GetParams(sdk.Context) authtypes.Params
}

<<<<<<< HEAD:testutil/e2e/interfaces.go
type SlashingKeeper interface {
=======
type TestSlashingKeeper interface {
>>>>>>> main:testutil/integration/interfaces.go
	ccvtypes.SlashingKeeper
	SetValidatorSigningInfo(ctx sdk.Context, address sdk.ConsAddress,
		info slashingtypes.ValidatorSigningInfo)
	SignedBlocksWindow(ctx sdk.Context) (res int64)
	HandleValidatorSignature(ctx sdk.Context, addr cryptotypes.Address, power int64, signed bool)
	MinSignedPerWindow(ctx sdk.Context) int64
	IterateValidatorMissedBlockBitArray(ctx sdk.Context,
		address sdk.ConsAddress, handler func(index int64, missed bool) (stop bool))
}

<<<<<<< HEAD:testutil/e2e/interfaces.go
type EvidenceKeeper interface {
	HandleEquivocationEvidence(ctx sdk.Context, evidence *evidencetypes.Equivocation)
}

type DistributionKeeper interface {
=======
type TestEvidenceKeeper interface {
	HandleEquivocationEvidence(ctx sdk.Context, evidence *evidencetypes.Equivocation)
}

type TestDistributionKeeper interface {
>>>>>>> main:testutil/integration/interfaces.go
	GetFeePoolCommunityCoins(ctx sdk.Context) sdk.DecCoins
	GetDistributionAccount(ctx sdk.Context) authtypes.ModuleAccountI
	GetValidatorOutstandingRewards(ctx sdk.Context,
		val sdk.ValAddress) (rewards distributiontypes.ValidatorOutstandingRewards)
	GetCommunityTax(ctx sdk.Context) (percent sdk.Dec)
}

<<<<<<< HEAD:testutil/e2e/interfaces.go
type MintKeeper interface {
	GetParams(ctx sdk.Context) (params minttypes.Params)
}

type GovKeeper interface {
	GetParams(ctx sdk.Context) govv1.Params
	SetParams(ctx sdk.Context, params govv1.Params) error
	// GetDepositParams(ctx sdk.Context) govv1.DepositParams
	// GetVotingParams(ctx sdk.Context) govv1.VotingParams
	// SetVotingParams(ctx sdk.Context, votingParams govv1.VotingParams)
	// SubmitProposal(ctx sdk.Context, content govv1beta1.Content) (govv1.Proposal, error)
	SubmitProposal(ctx sdk.Context, messages []sdk.Msg, metadata, title, summary string, proposer sdk.AccAddress) (govv1.Proposal, error)
=======
type TestMintKeeper interface {
	GetParams(ctx sdk.Context) (params minttypes.Params)
}

type TestGovKeeper interface {
	GetDepositParams(ctx sdk.Context) govtypes.DepositParams
	GetVotingParams(ctx sdk.Context) govtypes.VotingParams
	SetVotingParams(ctx sdk.Context, votingParams govtypes.VotingParams)
	SubmitProposal(ctx sdk.Context, content govtypes.Content) (govtypes.Proposal, error)
>>>>>>> main:testutil/integration/interfaces.go
	AddDeposit(ctx sdk.Context, proposalID uint64, depositorAddr sdk.AccAddress, depositAmount sdk.Coins) (bool, error)
	AddVote(ctx sdk.Context, proposalID uint64, voterAddr sdk.AccAddress, options govv1.WeightedVoteOptions, metadata string) error
}
