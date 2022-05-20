package consumer

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/interchain-security/x/ccv/consumer/keeper"
	tmtypes "github.com/tendermint/tendermint/types"
)

// TODO: export ccv vals as GenesisValidators
// WriteValidators returns a slice of bonded genesis validators.
func WriteValidators(ctx sdk.Context, keeper keeper.Keeper) (vals []tmtypes.GenesisValidator, err error) {

	return
}
