package types

import (
	ibctmtypes "github.com/cosmos/ibc-go/v7/modules/light-clients/07-tendermint"

	errorsmod "cosmossdk.io/errors"

	abci "github.com/cometbft/cometbft/abci/types"
)

// NewInitialConsumerGenesisState returns a ConsumerGenesisState for a completely new consumer chain.
func NewInitialConsumerGenesisState(cs *ibctmtypes.ClientState, consState *ibctmtypes.ConsensusState,
	initValSet []abci.ValidatorUpdate, params ConsumerParams,
) *ConsumerGenesisState {
	return &ConsumerGenesisState{
		NewChain: true,
		Params:   params,
		Provider: ProviderInfo{
			ClientState:    cs,
			ConsensusState: consState,
			InitialValSet:  initValSet,
		},
	}
}

// DefaultConsumerGenesisState returns a default disabled consumer chain genesis state. This allows the module to be hooked up to app without getting use
// unless explicitly specified in genesis.
func DefaultConsumerGenesisState() *ConsumerGenesisState {
	return &ConsumerGenesisState{
		Params: DefaultParams(),
	}
}

func (gs ConsumerGenesisState) Validate() error {
	if !gs.Params.Enabled {
		return nil
	}
	if len(gs.Provider.InitialValSet) == 0 {
		return errorsmod.Wrap(ErrInvalidGenesis, "initial validator set is empty")
	}
	if err := gs.Params.Validate(); err != nil {
		return err
	}

	if gs.NewChain {
		if gs.Provider.ClientState == nil {
			return errorsmod.Wrap(ErrInvalidGenesis, "provider client state cannot be nil for new chain")
		}
		if err := gs.Provider.ClientState.Validate(); err != nil {
			return errorsmod.Wrapf(ErrInvalidGenesis, "provider client state invalid for new chain %s", err.Error())
		}
		if gs.Provider.ConsensusState == nil {
			return errorsmod.Wrap(ErrInvalidGenesis, "provider consensus state cannot be nil for new chain")
		}
		if err := gs.Provider.ConsensusState.ValidateBasic(); err != nil {
			return errorsmod.Wrapf(ErrInvalidGenesis, "provider consensus state invalid for new chain %s", err.Error())
		}
	} else {
		if gs.Provider.ClientState != nil || gs.Provider.ConsensusState != nil {
			return errorsmod.Wrap(ErrInvalidGenesis, "provider client state and consensus state must be nil for a restarting genesis state")
		}
	}
	return nil
}
