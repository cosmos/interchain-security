package consumer_test

import (
	"encoding/json"
	"testing"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	"github.com/cosmos/cosmos-sdk/simapp"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/cosmos-sdk/x/staking/teststaking"
	ccvstakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	democracyapp "github.com/cosmos/interchain-security/app/consumer-democracy"
	"github.com/cosmos/interchain-security/x/ccv/consumer"
	"github.com/stretchr/testify/require"
	"github.com/tendermint/spm/cosmoscmd"
	abci "github.com/tendermint/tendermint/abci/types"
	"github.com/tendermint/tendermint/libs/log"
	tmproto "github.com/tendermint/tendermint/proto/tendermint/types"
	tmtypes "github.com/tendermint/tendermint/types"
	dbm "github.com/tendermint/tm-db"
)

// TODO: Determine if refactors are necessary for this test
func TestEndBlock(t *testing.T) {
	PKs := simapp.CreateTestPubKeys(500)
	validator1 := teststaking.NewValidator(t, sdk.ValAddress(PKs[0].Address().Bytes()), PKs[0])
	validator2 := teststaking.NewValidator(t, sdk.ValAddress(PKs[1].Address().Bytes()), PKs[1])
	_ = validator2

	tmPK1, err := cryptocodec.ToTmPubKeyInterface(PKs[0])
	require.NoError(t, err)
	tmValidator1 := tmtypes.NewValidator(tmPK1, 1)
	_ = tmValidator1

	tmPK2, err := cryptocodec.ToTmPubKeyInterface(PKs[1])
	require.NoError(t, err)
	tmValidator2 := tmtypes.NewValidator(tmPK2, 1)
	_ = tmValidator2

	tmPK3, err := cryptocodec.ToTmPubKeyInterface(PKs[2])
	require.NoError(t, err)
	tmValidator3 := tmtypes.NewValidator(tmPK3, 1)
	_ = tmValidator3

	testCases := []struct {
		name                string
		preCCV              bool
		sovereignValidators []ccvstakingtypes.Validator
		providerValidators  []abci.ValidatorUpdate
		expValUpdateLen     int
	}{
		{
			name:                "case not preCCV",
			preCCV:              false,
			sovereignValidators: []ccvstakingtypes.Validator{validator1},
			providerValidators:  []abci.ValidatorUpdate{tmtypes.TM2PB.ValidatorUpdate(tmValidator1)},
			expValUpdateLen:     1,
		},
		{
			name:                "case preCCV - no duplication with sovereign validators",
			preCCV:              true,
			sovereignValidators: []ccvstakingtypes.Validator{validator1, validator2},
			providerValidators:  []abci.ValidatorUpdate{tmtypes.TM2PB.ValidatorUpdate(tmValidator3)},
			expValUpdateLen:     3,
		},
		{
			name:                "case preCCV - duplication with sovereign validators",
			preCCV:              true,
			sovereignValidators: []ccvstakingtypes.Validator{validator1, validator2},
			providerValidators:  []abci.ValidatorUpdate{tmtypes.TM2PB.ValidatorUpdate(tmValidator2), tmtypes.TM2PB.ValidatorUpdate(tmValidator3)},
			expValUpdateLen:     3,
		},
	}

	for _, tc := range testCases {
		db := dbm.NewMemDB()
		encodingConfig := cosmoscmd.MakeEncodingConfig(democracyapp.ModuleBasics)
		appCodec := encodingConfig.Marshaler
		app := democracyapp.New(log.NewNopLogger(), db, nil, true, map[int64]bool{}, "", 5, encodingConfig, simapp.EmptyAppOptions{})
		dApp := app.(*democracyapp.App)
		ctx := dApp.BaseApp.NewContext(true, tmproto.Header{})

		genesisState := democracyapp.NewDefaultGenesisState(appCodec)
		stateBytes, err := json.MarshalIndent(genesisState, "", " ")
		if err != nil {
			panic(err)
		}

		app.InitChain(
			abci.RequestInitChain{
				Validators:      []abci.ValidatorUpdate{},
				ConsensusParams: simapp.DefaultConsensusParams,
				AppStateBytes:   stateBytes,
			},
		)

		dApp.StakingKeeper.SetParams(ctx, ccvstakingtypes.DefaultParams())
		for _, val := range tc.sovereignValidators {
			dApp.StakingKeeper.SetValidator(ctx, val)
			dApp.StakingKeeper.SetLastValidatorPower(ctx, val.GetOperator(), 1)
		}

		dApp.ConsumerKeeper.SetPreCCVTrue(ctx)
		dApp.ConsumerKeeper.SetInitialValSet(ctx, tc.providerValidators)
		consumerModule := consumer.NewAppModule(dApp.ConsumerKeeper, dApp.StakingKeeper)

		valUpdate := consumerModule.EndBlock(
			ctx,
			abci.RequestEndBlock{},
		)

		// check returned initial validators are expected values
		require.Len(t, valUpdate, tc.expValUpdateLen)
		// check preCCV deleted after the execution
		require.False(t, dApp.ConsumerKeeper.IsPreCCV(ctx))
	}
}
