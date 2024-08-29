package keeper

import (
	"fmt"

	sdk "github.com/cosmos/cosmos-sdk/types"

	abci "github.com/cometbft/cometbft/abci/types"

	"github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/v5/x/ccv/types"
)

// InitGenesis initializes the CCV provider state and binds to PortID.
func (k Keeper) InitGenesis(ctx sdk.Context, genState *types.GenesisState) []abci.ValidatorUpdate {
	k.SetPort(ctx, ccv.ProviderPortID)

	// Only try to bind to port if it is not already bound, since we may already own
	// port capability from capability InitGenesis
	if !k.IsBound(ctx, ccv.ProviderPortID) {
		// CCV module binds to the provider port on InitChain
		// and claims the returned capability
		err := k.BindPort(ctx, ccv.ProviderPortID)
		if err != nil {
			// If the binding fails, the chain MUST NOT start
			panic(fmt.Errorf("could not claim port capability: %w", err))
		}
	}

	k.SetValidatorSetUpdateId(ctx, genState.ValsetUpdateId)
	for _, v2h := range genState.ValsetUpdateIdToHeight {
		k.SetValsetUpdateBlockHeight(ctx, v2h.ValsetUpdateId, v2h.Height)
	}

	// Set initial state for each consumer chain
	for _, cs := range genState.ConsumerStates {
		chainID := cs.ChainId
		k.SetConsumerClientId(ctx, chainID, cs.ClientId)
		if err := k.SetConsumerGenesis(ctx, chainID, cs.ConsumerGenesis); err != nil {
			// An error here would indicate something is very wrong,
			// the ConsumerGenesis validated in ConsumerState.Validate().
			panic(fmt.Errorf("consumer chain genesis could not be persisted: %w", err))
		}
		// check if the CCV channel was established
		if cs.ChannelId != "" {
			k.SetChannelToConsumerId(ctx, cs.ChannelId, chainID)
			k.SetConsumerIdToChannelId(ctx, chainID, cs.ChannelId)
			k.SetInitChainHeight(ctx, chainID, cs.InitialHeight)
			k.SetSlashAcks(ctx, cs.ChainId, cs.SlashDowntimeAck)
		} else {
			k.AppendPendingVSCPackets(ctx, chainID, cs.PendingValsetChanges...)
		}
	}

	// Import key assignment state
	for _, item := range genState.ValidatorConsumerPubkeys {
		providerAddr := types.NewProviderConsAddress(item.ProviderAddr)
		k.SetValidatorConsumerPubKey(ctx, item.ChainId, providerAddr, *item.ConsumerKey)
	}

	for _, item := range genState.ValidatorsByConsumerAddr {
		consumerAddr := types.NewConsumerConsAddress(item.ConsumerAddr)
		providerAddr := types.NewProviderConsAddress(item.ProviderAddr)
		k.SetValidatorByConsumerAddr(ctx, item.ChainId, consumerAddr, providerAddr)
	}

	for _, item := range genState.ConsumerAddrsToPruneV2 {
		for _, addr := range item.ConsumerAddrs.Addresses {
			consumerAddr := types.NewConsumerConsAddress(addr)
			k.AppendConsumerAddrsToPrune(ctx, item.ChainId, item.PruneTs, consumerAddr)
		}
	}

	k.SetParams(ctx, genState.Params)
	k.InitializeSlashMeter(ctx)

	return k.InitGenesisValUpdates(ctx)
}

// InitGenesisValUpdates returns the genesis validator set updates
// for the provider module by selecting the first MaxProviderConsensusValidators
// from the staking module's validator set.
func (k Keeper) InitGenesisValUpdates(ctx sdk.Context) []abci.ValidatorUpdate {
	// get the staking validator set
	valSet, err := k.stakingKeeper.GetBondedValidatorsByPower(ctx)
	if err != nil {
		panic(fmt.Errorf("retrieving validator set: %w", err))
	}

	// restrict the set to the first MaxProviderConsensusValidators
	maxVals := k.GetMaxProviderConsensusValidators(ctx)
	if int64(len(valSet)) > maxVals {
		k.Logger(ctx).Info(fmt.Sprintf("reducing validator set from %d to %d", len(valSet), maxVals))
		valSet = valSet[:maxVals]
	}

	reducedValSet := make([]types.ConsensusValidator, len(valSet))
	for i, val := range valSet {
		consensusVal, err := k.CreateProviderConsensusValidator(ctx, val)
		if err != nil {
			k.Logger(ctx).Error(fmt.Sprintf("failed to create provider consensus validator: %v", err))
			continue
		}
		reducedValSet[i] = consensusVal
	}

	k.SetLastProviderConsensusValSet(ctx, reducedValSet)

	valUpdates := make([]abci.ValidatorUpdate, len(reducedValSet))
	for i, val := range reducedValSet {
		valUpdates[i] = abci.ValidatorUpdate{
			PubKey: *val.PublicKey,
			Power:  val.Power,
		}
	}
	return valUpdates
}

// ExportGenesis returns the CCV provider module's exported genesis
func (k Keeper) ExportGenesis(ctx sdk.Context) *types.GenesisState {
	// get a list of all registered consumer chains
	registeredConsumerIds := k.GetAllRegisteredConsumerIds(ctx)

	// export states for each consumer chains
	var consumerStates []types.ConsumerState
	for _, consumerId := range registeredConsumerIds {
		// no need for the second return value of GetConsumerClientId
		// as GetAllRegisteredConsumerIds already iterated through
		// the entire prefix range
		clientId, _ := k.GetConsumerClientId(ctx, consumerId)
		gen, found := k.GetConsumerGenesis(ctx, consumerId)
		if !found {
			panic(fmt.Errorf("cannot find genesis for consumer chain %s with client %s", consumerId, clientId))
		}

		// initial consumer chain states
		cs := types.ConsumerState{
			ChainId:         consumerId,
			ClientId:        clientId,
			ConsumerGenesis: gen,
		}

		// try to find channel id for the current consumer chain
		channelId, found := k.GetConsumerIdToChannelId(ctx, consumerId)
		if found {
			cs.ChannelId = channelId
			cs.InitialHeight, found = k.GetInitChainHeight(ctx, consumerId)
			if !found {
				panic(fmt.Errorf("cannot find init height for consumer chain %s", consumerId))
			}
			cs.SlashDowntimeAck = k.GetSlashAcks(ctx, consumerId)
		}

		cs.PendingValsetChanges = k.GetPendingVSCPackets(ctx, consumerId)
		consumerStates = append(consumerStates, cs)
	}

	// ConsumerAddrsToPrune are added only for registered consumer chains
	consumerAddrsToPrune := []types.ConsumerAddrsToPruneV2{}
	for _, chainID := range registeredConsumerIds {
		consumerAddrsToPrune = append(consumerAddrsToPrune, k.GetAllConsumerAddrsToPrune(ctx, chainID)...)
	}

	params := k.GetParams(ctx)

	// TODO (PERMISSIONLESS)
	return types.NewGenesisState(
		k.GetValidatorSetUpdateId(ctx),
		k.GetAllValsetUpdateBlockHeights(ctx),
		consumerStates,
		params,
		k.GetAllValidatorConsumerPubKeys(ctx, nil),
		k.GetAllValidatorsByConsumerAddr(ctx, nil),
		consumerAddrsToPrune,
	)
}
