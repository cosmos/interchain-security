package e2e

import (
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
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
}

// The interface that any consumer app must implement to be compatible with e2e tests
// This is a wrapper around the ibc testing app interface with additional constraints.
type ConsumerApp interface {
	ibctesting.TestingApp
	GetConsumerKeeper() consumerkeeper.Keeper
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
}

type E2eBankKeeper interface {
	ccvtypes.BankKeeper
	// mas, or is this not needed?
}
