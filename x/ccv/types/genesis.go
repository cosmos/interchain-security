package types

import (
	"strings"

	ibctmtypes "github.com/cosmos/ibc-go/v10/modules/light-clients/07-tendermint"

	errorsmod "cosmossdk.io/errors"

	abci "github.com/cometbft/cometbft/abci/types"
)

// NewInitialConsumerGenesisState returns a ConsumerGenesisState for a completely new consumer chain.
func NewInitialConsumerGenesisState(
	cs *ibctmtypes.ClientState,
	consState *ibctmtypes.ConsensusState,
	initValSet []abci.ValidatorUpdate,
	preCCV bool,
	connectionId string,
	params ConsumerParams,
) *ConsumerGenesisState {
	return &ConsumerGenesisState{
		NewChain: true,
		Params:   params,
		Provider: ProviderInfo{
			ClientState:    cs,
			ConsensusState: consState,
			InitialValSet:  initValSet,
		},
		PreCCV:       preCCV,
		ConnectionId: connectionId,
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
	if !gs.NewChain {
		// consumer genesis should be for a new chain only
		return errorsmod.Wrapf(ErrInvalidGenesis, "NewChain must be set to true")
	}

	if gs.PreCCV {
		// consumer chain MUST start in pre-CCV state, i.e.,
		// the consumer CCV module MUST NOT pass validator updates
		// to the underlying consensus engine
		if gs.Provider.ClientState != nil || gs.Provider.ConsensusState != nil {
			return errorsmod.Wrap(ErrInvalidGenesis, "provider client state and consensus state must be nil for a restarting genesis state")
		}
		if err := ValidateConnectionIdentifier(gs.ConnectionId); err != nil {
			return errorsmod.Wrapf(ErrInvalidGenesis, "ConnectionId: %s", err.Error())
		}
		if strings.TrimSpace(gs.ConnectionId) == "" {
			return errorsmod.Wrapf(ErrInvalidGenesis, "ConnectionId cannot be empty when preCCV is true")
		}
	} else {
		// consumer chain MUST NOT start in pre-CCV state, i.e.,
		// the consumer CCV module MUST pass validator updates
		// to the underlying consensus engine
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
		if strings.TrimSpace(gs.ConnectionId) != "" {
			return errorsmod.Wrapf(ErrInvalidGenesis, "ConnectionId must be empty when preCCV is false")
		}
	}
	return nil
}
