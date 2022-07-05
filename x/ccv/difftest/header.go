package difftest

import (
	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"
	ibctesting "github.com/cosmos/ibc-go/v3/testing"
	tmtypes "github.com/tendermint/tendermint/types"

	"github.com/cosmos/cosmos-sdk/x/staking/teststaking"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
)

func GetValsAtHeight(histInfo map[int64]stakingtypes.HistoricalInfo, chain *ibctesting.TestChain, height int64) (*tmtypes.ValidatorSet, bool) {
	valSet := stakingtypes.Validators(histInfo[height].Valset)
	if valSet == nil {
		panic("nil val set")
	}

	tmValidators, err := teststaking.ToTmValidators(valSet, sdk.DefaultPowerReduction)
	if err != nil {
		panic(err)
	}
	return tmtypes.NewValidatorSet(tmValidators), true
}

func Header(histInfo map[int64]stakingtypes.HistoricalInfo, chain *ibctesting.TestChain, counterparty *ibctesting.TestChain, clientID string) (*ibctmtypes.Header, error) {
	header := counterparty.LastHeader
	// Relayer must query for LatestHeight on client to get TrustedHeight if the trusted height is not set
	trustedHeight := chain.GetClientState(clientID).GetLatestHeight().(clienttypes.Height)
	var (
		tmTrustedVals *tmtypes.ValidatorSet
		ok            bool
	)
	// Once we get TrustedHeight from client, we must query the validators from the counterparty chain
	// If the LatestHeight == LastHeader.Height, then TrustedValidators are current validators
	// If LatestHeight < LastHeader.Height, we can query the historical validator set from HistoricalInfo
	if trustedHeight == counterparty.LastHeader.GetHeight() {
		tmTrustedVals = counterparty.Vals
	} else {
		// NOTE: We need to get validators from counterparty at height: trustedHeight+1
		// since the last trusted validators for a header at height h
		// is the NextValidators at h+1 committed to in header h by
		// NextValidatorsHash
		tmTrustedVals, ok = GetValsAtHeight(histInfo, counterparty, int64(trustedHeight.RevisionHeight+1))
		if !ok {
			return nil, sdkerrors.Wrapf(ibctmtypes.ErrInvalidHeaderHeight, "could not retrieve trusted validators at trustedHeight: %d", trustedHeight)
		}
	}
	// inject trusted fields into last header
	// for now assume revision number is 0
	header.TrustedHeight = trustedHeight

	trustedVals, err := tmTrustedVals.ToProto()
	if err != nil {
		return nil, err
	}
	header.TrustedValidators = trustedVals

	return header, nil
}
