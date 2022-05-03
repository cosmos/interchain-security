package keeper

import (
	"encoding/binary"
	"strings"
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	commitmenttypes "github.com/cosmos/ibc-go/v3/modules/core/23-commitment/types"
	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
	abci "github.com/tendermint/tendermint/abci/types"

	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
)

// CreateConsumerChainProposal will receive the consumer chain's client state from the proposal.
// If the spawn time has already passed, then set the consumer chain. Otherwise store the client
// as a pending client, and set once spawn time has passed.
func (k Keeper) CreateConsumerChainProposal(ctx sdk.Context, p *types.CreateConsumerChainProposal) error {
	if ctx.BlockTime().After(p.SpawnTime) {
		return k.CreateConsumerClient(ctx, p.ChainId, p.InitialHeight)
	}

	k.SetPendingClientInfo(ctx, p.SpawnTime, p.ChainId, p.InitialHeight)
	return nil
}

// CreateConsumerClient will create the CCV client for the given consumer chain. The CCV channel must be built
// on top of the CCV client to ensure connection with the right consumer chain.
func (k Keeper) CreateConsumerClient(ctx sdk.Context, chainID string, initialHeight clienttypes.Height) error {
	unbondingTime := k.stakingKeeper.UnbondingTime(ctx)

	// create clientstate by getting template client from parameters and filling in zeroed fields from proposal.
	clientState := k.GetTemplateClient(ctx)
	clientState.ChainId = chainID
	clientState.LatestHeight = initialHeight
	clientState.TrustingPeriod = unbondingTime / 2
	clientState.UnbondingPeriod = unbondingTime

	// TODO: Allow for current validators to set different keys
	consensusState := ibctmtypes.NewConsensusState(ctx.BlockTime(), commitmenttypes.NewMerkleRoot([]byte(ibctmtypes.SentinelRoot)), ctx.BlockHeader().NextValidatorsHash)
	clientID, err := k.clientKeeper.CreateClient(ctx, clientState, consensusState)
	if err != nil {
		return err
	}

	k.SetConsumerClient(ctx, chainID, clientID)
	consumerGen, err := k.MakeConsumerGenesis(ctx)
	if err != nil {
		return err
	}

	k.SetConsumerGenesis(ctx, chainID, consumerGen)
	return nil
}

func (k Keeper) MakeConsumerGenesis(ctx sdk.Context) (gen consumertypes.GenesisState, err error) {
	unbondingTime := k.stakingKeeper.UnbondingTime(ctx)
	height := clienttypes.GetSelfHeight(ctx)

	clientState := k.GetTemplateClient(ctx)
	clientState.ChainId = ctx.ChainID()
	clientState.LatestHeight = height //(+-1???)
	clientState.TrustingPeriod = unbondingTime / 2
	clientState.UnbondingPeriod = unbondingTime

	consState, err := k.clientKeeper.GetSelfConsensusState(ctx, height)
	if err != nil {
		return gen, sdkerrors.Wrapf(clienttypes.ErrConsensusStateNotFound, "error %s getting self consensus state for: %s", err, height)
	}

	gen = *childtypes.DefaultGenesisState()

	gen.Params.Enabled = true
	gen.NewChain = true
	gen.ProviderClientState = clientState
	gen.ProviderConsensusState = consState.(*ibctmtypes.ConsensusState)

	var lastPowers []stakingtypes.LastValidatorPower

	k.stakingKeeper.IterateLastValidatorPowers(ctx, func(addr sdk.ValAddress, power int64) (stop bool) {
		lastPowers = append(lastPowers, stakingtypes.LastValidatorPower{Address: addr.String(), Power: power})
		return false
	})

	updates := []abci.ValidatorUpdate{}

	for _, p := range lastPowers {
		addr, err := sdk.ValAddressFromBech32(p.Address)
		if err != nil {
			panic(err)
		}

		val, found := k.stakingKeeper.GetValidator(ctx, addr)
		if !found {
			panic("Validator from LastValidatorPowers not found in staking keeper")
		}

		tmProtoPk, err := val.TmConsPublicKey()
		if err != nil {
			panic(err)
		}

		updates = append(updates, abci.ValidatorUpdate{
			PubKey: tmProtoPk,
			Power:  p.Power,
		})
	}

	gen.InitialValSet = updates

	return gen, nil
}

// SetConsumerClient sets the clientID for the given chainID
func (k Keeper) SetConsumerClient(ctx sdk.Context, chainID, clientID string) {
	store := ctx.KVStore(k.storeKey)
	store.Set(types.ChainToClientKey(chainID), []byte(clientID))
}

// GetConsumerClient returns the clientID for the given chainID.
func (k Keeper) GetConsumerClient(ctx sdk.Context, chainID string) string {
	store := ctx.KVStore(k.storeKey)
	return string(store.Get(types.ChainToClientKey(chainID)))
}

// SetPendingClientInfo sets the initial height for the given timestamp and chainID
func (k Keeper) SetPendingClientInfo(ctx sdk.Context, timestamp time.Time, chainID string, initialHeight clienttypes.Height) error {
	store := ctx.KVStore(k.storeKey)
	bz, err := k.cdc.Marshal(&initialHeight)
	if err != nil {
		return err
	}
	store.Set(types.PendingClientKey(timestamp, chainID), bz)
	return nil
}

// GetPendingClient gets the initial height for the given timestamp and chainID
func (k Keeper) GetPendingClientInfo(ctx sdk.Context, timestamp time.Time, chainID string) clienttypes.Height {
	store := ctx.KVStore(k.storeKey)
	bz := store.Get(types.PendingClientKey(timestamp, chainID))
	if len(bz) == 0 {
		return clienttypes.Height{}
	}
	var initialHeight clienttypes.Height
	k.cdc.MustUnmarshal(bz, &initialHeight)
	return initialHeight
}

// IteratePendingClientInfo iterates over the pending client info in order and creates the consumer client if the spawn time has passed,
// otherwise it will break out of loop and return.
func (k Keeper) IteratePendingClientInfo(ctx sdk.Context) {
	store := ctx.KVStore(k.storeKey)
	iterator := sdk.KVStorePrefixIterator(store, []byte(types.PendingClientKeyPrefix+"/"))
	defer iterator.Close()

	if !iterator.Valid() {
		return
	}

	for ; iterator.Valid(); iterator.Next() {
		suffixKey := iterator.Key()
		// splitKey contains the bigendian time in the first element and the chainID in the second element/
		splitKey := strings.Split(string(suffixKey), "/")

		timeNano := binary.BigEndian.Uint64([]byte(splitKey[0]))
		spawnTime := time.Unix(0, int64(timeNano))
		var initialHeight clienttypes.Height
		k.cdc.MustUnmarshal(iterator.Value(), &initialHeight)

		if ctx.BlockTime().After(spawnTime) {
			k.CreateConsumerClient(ctx, splitKey[1], initialHeight)
		} else {
			break
		}
	}
}
