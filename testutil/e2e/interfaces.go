package e2e

import (
	"time"

	cryptotypes "github.com/cosmos/cosmos-sdk/crypto/types"
	sdk "github.com/cosmos/cosmos-sdk/types"
	evidencetypes "github.com/cosmos/cosmos-sdk/x/evidence/types"
	paramstypes "github.com/cosmos/cosmos-sdk/x/params/types"
	slashingtypes "github.com/cosmos/cosmos-sdk/x/slashing/types"
	"github.com/cosmos/cosmos-sdk/x/staking/types"
	ibctesting "github.com/cosmos/ibc-go/v3/testing"
	consumerkeeper "github.com/cosmos/interchain-security/x/ccv/consumer/keeper"
	providerkeeper "github.com/cosmos/interchain-security/x/ccv/provider/keeper"
	ccvtypes "github.com/cosmos/interchain-security/x/ccv/types"
)

// The interface that any provider app must implement to be compatible with ccv e2e tests.
// This is a wrapper around the ibc testing app interface with additional constraints.
type ProviderApp interface {
	ibctesting.TestingApp
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
	GetConsumerKeeper() consumerkeeper.Keeper
	GetSubspace(moduleName string) paramstypes.Subspace
	// Returns a bank keeper interface with more capabilities than the expected_keepers interface
	GetE2eBankKeeper() E2eBankKeeper
	// Returns an account keeper interface with more capabilities than the expected_keepers interface
	GetE2eAccountKeeper() E2eAccountKeeper
	// Returns a slashing keeper interface with more capabilities than the expected_keepers interface
	GetE2eSlashingKeeper() E2eSlashingKeeper
	// Returns an evidence keeper interface with more capabilities than the expected_keepers interface
	GetE2eEvidenceKeeper() E2eEvidenceKeeper
}

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
}

type E2eBankKeeper interface {
	ccvtypes.BankKeeper
	SendCoinsFromAccountToModule(ctx sdk.Context, senderAddr sdk.AccAddress,
		recipientModule string, amt sdk.Coins) error
}

type E2eAccountKeeper interface {
	// Might just be the expected interface but defined here for consistency since only used in e2e
	ccvtypes.AccountKeeper
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
}
