package governance

import (
	"fmt"
	"reflect"

	"github.com/cosmos/cosmos-sdk/codec"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/cosmos-sdk/types/module"

	abci "github.com/cometbft/cometbft/abci/types"
	bankkeeper "github.com/cosmos/cosmos-sdk/x/bank/keeper"
	banktypes "github.com/cosmos/cosmos-sdk/x/bank/types"
	distrkeeper "github.com/cosmos/cosmos-sdk/x/distribution/keeper"
	distrtypes "github.com/cosmos/cosmos-sdk/x/distribution/types"
	gov "github.com/cosmos/cosmos-sdk/x/gov"
	"github.com/cosmos/cosmos-sdk/x/gov/keeper"
	govkeeper "github.com/cosmos/cosmos-sdk/x/gov/keeper"
	govtypes "github.com/cosmos/cosmos-sdk/x/gov/types"
	govv1 "github.com/cosmos/cosmos-sdk/x/gov/types/v1"
	govv1beta1 "github.com/cosmos/cosmos-sdk/x/gov/types/v1beta1"
	mintkeeper "github.com/cosmos/cosmos-sdk/x/mint/keeper"
	minttypes "github.com/cosmos/cosmos-sdk/x/mint/types"
	stakingkeeper "github.com/cosmos/cosmos-sdk/x/staking/keeper"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
)

const (
	AttributeValueProposalForbidden = "proposal_forbidden"
)

var (
	_ module.AppModule           = AppModule{}
	_ module.AppModuleSimulation = AppModule{}
)

// AppModule embeds the Cosmos SDK's x/governance AppModule
type AppModule struct {
	// embed the Cosmos SDK's x/governance AppModule
	gov.AppModule

	keeper                      keeper.Keeper
	keeperMap                   map[string]interface{}
	isLegacyProposalWhitelisted func(govv1beta1.Content) bool
	isParamChangeWhitelisted    func(map[ParamChangeKey]struct{}) bool
	isModuleWhiteList           func(string) bool
}

type ParamChangeKey struct {
	MsgType, Key string
}

// NewAppModule creates a new AppModule object using the native x/governance module AppModule constructor.
func NewAppModule(cdc codec.Codec,
	keeper keeper.Keeper,
	ak govtypes.AccountKeeper,
	bk govtypes.BankKeeper,
	isProposalWhitelisted func(govv1beta1.Content) bool,
	IsParamChangeWhitelisted func(map[ParamChangeKey]struct{}) bool,
	ss govtypes.ParamSubspace,
	keeperMap map[string]interface{},
	isModuleWhiteList func(string) bool,
) AppModule {
	govAppModule := gov.NewAppModule(cdc, &keeper, ak, bk, ss)
	return AppModule{
		AppModule:                   govAppModule,
		keeper:                      keeper,
		isLegacyProposalWhitelisted: isProposalWhitelisted,
		isParamChangeWhitelisted:    IsParamChangeWhitelisted,
		keeperMap:                   keeperMap,
		isModuleWhiteList:           isModuleWhiteList,
	}
}

func (am AppModule) EndBlock(ctx sdk.Context, request abci.RequestEndBlock) []abci.ValidatorUpdate {
	am.keeper.IterateActiveProposalsQueue(ctx, ctx.BlockHeader().Time, func(proposal govv1.Proposal) bool {
		// if there are forbidden proposals in active proposals queue, refund deposit, delete votes for that proposal
		// and delete proposal from all storages
		deleteForbiddenProposal(ctx, am, proposal)
		return false
	})

	return am.AppModule.EndBlock(ctx, request)
}

func GetChangeParamsKey(currentParams, newParams any, typeUrl string) map[ParamChangeKey]struct{} {
	keys := map[ParamChangeKey]struct{}{}

	currentValues := reflect.ValueOf(currentParams)
	currentTypes := currentValues.Type()

	newValues := reflect.ValueOf(newParams)

	for i := 0; i < currentValues.NumField(); i++ {
		if !reflect.DeepEqual(currentValues.Field(i).Interface(), newValues.Field(i).Interface()) {
			keys[ParamChangeKey{MsgType: typeUrl, Key: currentTypes.Field(i).Name}] = struct{}{}
		}
	}

	return keys
}

func deleteForbiddenProposal(ctx sdk.Context, am AppModule, proposal govv1.Proposal) {
	messages := proposal.GetMessages()
	var breakFlag bool = true

	for _, message := range messages {
		sdkMsg, ok := message.GetCachedValue().(*govv1.MsgExecLegacyContent)
		if !ok {
			if am.isModuleWhiteList(message.TypeUrl) {
				m := message.GetCachedValue()
				switch m.(type) {
				case *minttypes.MsgUpdateParams:
					p := m.(*minttypes.MsgUpdateParams).Params
					keeper := am.keeperMap[message.TypeUrl]
					param := keeper.(mintkeeper.Keeper).GetParams(ctx)
					keys := GetChangeParamsKey(p, param, message.TypeUrl)
					if !am.isParamChangeWhitelisted(keys) {
						breakFlag = false
					}
				case *banktypes.MsgUpdateParams:
					p := m.(*banktypes.MsgUpdateParams).Params
					keeper := am.keeperMap[message.TypeUrl]
					param := keeper.(bankkeeper.Keeper).GetParams(ctx)
					keys := GetChangeParamsKey(p, param, message.TypeUrl)
					if !am.isParamChangeWhitelisted(keys) {
						breakFlag = false
					}
				case *distrtypes.MsgUpdateParams:
					p := m.(*distrtypes.MsgUpdateParams).Params
					keeper := am.keeperMap[message.TypeUrl]
					param := keeper.(distrkeeper.Keeper).GetParams(ctx)
					keys := GetChangeParamsKey(p, param, message.TypeUrl)
					if !am.isParamChangeWhitelisted(keys) {
						breakFlag = false
					}
				case *stakingtypes.MsgUpdateParams:
					p := m.(*stakingtypes.MsgUpdateParams).Params
					keeper := am.keeperMap[message.TypeUrl]
					param := keeper.(stakingkeeper.Keeper).GetParams(ctx)
					keys := GetChangeParamsKey(p, param, message.TypeUrl)
					if !am.isParamChangeWhitelisted(keys) {
						breakFlag = false
					}
				case *govv1.MsgUpdateParams:
					p := m.(*govv1.MsgUpdateParams).Params
					keeper := am.keeperMap[message.TypeUrl]
					param := keeper.(govkeeper.Keeper).GetParams(ctx)
					keys := GetChangeParamsKey(p, param, message.TypeUrl)
					if !am.isParamChangeWhitelisted(keys) {
						breakFlag = false
					}
				default:
					breakFlag = false
				}
			} else {
				breakFlag = false
			}
		} else {
			content, err := govv1.LegacyContentFromMessage(sdkMsg)
			if err != nil {
				continue
			}
			if !am.isLegacyProposalWhitelisted(content) {
				breakFlag = false
			}
		}
	}

	if breakFlag {
		return
	}

	// delete the votes related to the proposal calling Tally
	// Tally's return result won't be used in decision if the tokens will be burned or refunded (they are always refunded), but
	// this function needs to be called to delete the votes related to the given proposal, since the deleteVote function is
	// private and cannot be called directly from the overridden app module
	am.keeper.Tally(ctx, proposal)

	am.keeper.DeleteProposal(ctx, proposal.Id)
	am.keeper.RefundAndDeleteDeposits(ctx, proposal.Id)

	ctx.EventManager().EmitEvent(
		sdk.NewEvent(
			govtypes.EventTypeActiveProposal,
			sdk.NewAttribute(govtypes.AttributeKeyProposalID, fmt.Sprintf("%d", proposal.Id)),
			sdk.NewAttribute(govtypes.AttributeKeyProposalResult, AttributeValueProposalForbidden),
		),
	)

	logger := am.keeper.Logger(ctx)
	logger.Info(
		"proposal is not whitelisted; deleted",
		"proposal", proposal.Id,
		"title", proposal.GetTitle(),
		"total_deposit", proposal.TotalDeposit)
}
