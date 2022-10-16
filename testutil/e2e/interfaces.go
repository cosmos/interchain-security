package e2e

import (
	"time"

	cryptotypes "github.com/cosmos/cosmos-sdk/crypto/types"
	sdk "github.com/cosmos/cosmos-sdk/types"
	authtypes "github.com/cosmos/cosmos-sdk/x/auth/types"
	distributiontypes "github.com/cosmos/cosmos-sdk/x/distribution/types"
	evidencetypes "github.com/cosmos/cosmos-sdk/x/evidence/types"
	govtypes "github.com/cosmos/cosmos-sdk/x/gov/types"
	minttypes "github.com/cosmos/cosmos-sdk/x/mint/types"
	paramstypes "github.com/cosmos/cosmos-sdk/x/params/types"
	slashingtypes "github.com/cosmos/cosmos-sdk/x/slashing/types"
	"github.com/cosmos/cosmos-sdk/x/staking/types"
	ibctesting "github.com/cosmos/ibc-go/v3/testing"
	consumerkeeper "github.com/cosmos/interchain-security/x/ccv/consumer/keeper"
	providerkeeper "github.com/cosmos/interchain-security/x/ccv/provider/keeper"
	ccvtypes "github.com/cosmos/interchain-security/x/ccv/types"
	abci "github.com/tendermint/tendermint/abci/types"
)

// The interface that any provider app must implement to be compatible with ccv e2e tests.
// This is a wrapper around the ibc testing app interface with additional constraints.
type ProviderApp interface {
	ibctesting.TestingApp

	//
	// Keeper getters
	//

	GetProviderKeeper() providerkeeper.Keeper
	// Returns a staking keeper interface with more capabilities than the expected_keepers interface
	GetE2eStakingKeeper() E2eStakingKeeper
	// Returns a bank keeper interface with more capabilities than the expected_keepers interface
	GetE2eBankKeeper() E2eBankKeeper
	// Returns a slashing keeper interface with more capabilities than the expected_keepers interface
	GetE2eSlashingKeeper() E2eSlashingKeeper
	// Returns a distribution keeper interface with more capabilities than the expected_keepers interface
	GetE2eDistributionKeeper() E2eDistributionKeeper
}

// The interface that any consumer app must implement to be compatible with e2e tests
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
	GetE2eBankKeeper() E2eBankKeeper
	// Returns an account keeper interface with more capabilities than the expected_keepers interface
	GetE2eAccountKeeper() E2eAccountKeeper
	// Returns a slashing keeper interface with more capabilities than the expected_keepers interface
	GetE2eSlashingKeeper() E2eSlashingKeeper
	// Returns an evidence keeper interface with more capabilities than the expected_keepers interface
	GetE2eEvidenceKeeper() E2eEvidenceKeeper
}

type DemocConsumerApp interface {
	ConsumerApp
	// Returns a distribution keeper interface with more capabilities than the expected_keepers interface
	GetE2eDistributionKeeper() E2eDistributionKeeper
	// Returns a staking keeper interface with more capabilities than the expected_keepers interface
	GetE2eStakingKeeper() E2eStakingKeeper
	// Returns a mint keeper interface with more capabilities than the expected_keepers interface
	GetE2eMintKeeper() E2eMintKeeper
	// Returns a gov keeper interface with more capabilities than the expected_keepers interface
	GetE2eGovKeeper() E2eGovKeeper
}

//
// The following keeper interfaces are wrappers around the expected keepers for ccv modules,
// since e2e tests require extra functionality from external keepers.
//

type E2eStakingKeeper interface {
	ccvtypes.StakingKeeper
	Delegate(ctx sdk.Context, delAddr sdk.AccAddress, bondAmt sdk.Int, tokenSrc types.BondStatus,
		validator types.Validator, subtractAccount bool) (newShares sdk.Dec, err error)
	Undelegate(ctx sdk.Context, delAddr sdk.AccAddress, valAddr sdk.ValAddress, sharesAmount sdk.Dec,
	) (time.Time, error)
	BeginRedelegation(ctx sdk.Context, delAddr sdk.AccAddress, valSrcAddr, valDstAddr sdk.ValAddress,
		sharesAmount sdk.Dec) (completionTime time.Time, err error)
	GetUnbondingDelegationByUnbondingId(ctx sdk.Context, id uint64,
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

type E2eBankKeeper interface {
	ccvtypes.BankKeeper
	SendCoinsFromAccountToModule(ctx sdk.Context, senderAddr sdk.AccAddress,
		recipientModule string, amt sdk.Coins) error
}

type E2eAccountKeeper interface {
	ccvtypes.AccountKeeper
	GetParams(sdk.Context) authtypes.Params
}

type E2eSlashingKeeper interface {
	ccvtypes.SlashingKeeper
	SetValidatorSigningInfo(ctx sdk.Context, address sdk.ConsAddress,
		info slashingtypes.ValidatorSigningInfo)
	SignedBlocksWindow(ctx sdk.Context) (res int64)
	HandleValidatorSignature(ctx sdk.Context, addr cryptotypes.Address, power int64, signed bool)
	MinSignedPerWindow(ctx sdk.Context) int64
	IterateValidatorMissedBlockBitArray(ctx sdk.Context,
		address sdk.ConsAddress, handler func(index int64, missed bool) (stop bool))
}

type E2eEvidenceKeeper interface {
	HandleEquivocationEvidence(ctx sdk.Context, evidence *evidencetypes.Equivocation)
}

type E2eDistributionKeeper interface {
	GetFeePoolCommunityCoins(ctx sdk.Context) sdk.DecCoins
	GetDistributionAccount(ctx sdk.Context) authtypes.ModuleAccountI
	GetValidatorOutstandingRewards(ctx sdk.Context,
		val sdk.ValAddress) (rewards distributiontypes.ValidatorOutstandingRewards)
	GetCommunityTax(ctx sdk.Context) (percent sdk.Dec)
}

type E2eMintKeeper interface {
	GetParams(ctx sdk.Context) (params minttypes.Params)
}

type E2eGovKeeper interface {
	GetDepositParams(ctx sdk.Context) govtypes.DepositParams
	GetVotingParams(ctx sdk.Context) govtypes.VotingParams
	SetVotingParams(ctx sdk.Context, votingParams govtypes.VotingParams)
	SubmitProposal(ctx sdk.Context, content govtypes.Content) (govtypes.Proposal, error)
	AddDeposit(ctx sdk.Context, proposalID uint64, depositorAddr sdk.AccAddress, depositAmount sdk.Coins) (bool, error)
	AddVote(ctx sdk.Context, proposalID uint64, voterAddr sdk.AccAddress, options govtypes.WeightedVoteOptions) error
}
