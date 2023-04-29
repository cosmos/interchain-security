package ante

import (
	"fmt"

	sdk "github.com/cosmos/cosmos-sdk/types"

	bankkeeper "github.com/cosmos/cosmos-sdk/x/bank/keeper"
	banktypes "github.com/cosmos/cosmos-sdk/x/bank/types"
	distrkeeper "github.com/cosmos/cosmos-sdk/x/distribution/keeper"
	distrtypes "github.com/cosmos/cosmos-sdk/x/distribution/types"
	govkeeper "github.com/cosmos/cosmos-sdk/x/gov/keeper"
	govv1 "github.com/cosmos/cosmos-sdk/x/gov/types/v1"
	govv1beta1 "github.com/cosmos/cosmos-sdk/x/gov/types/v1beta1"
	mintkeeper "github.com/cosmos/cosmos-sdk/x/mint/keeper"
	minttypes "github.com/cosmos/cosmos-sdk/x/mint/types"
	stakingkeeper "github.com/cosmos/cosmos-sdk/x/staking/keeper"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	ccvgov "github.com/cosmos/interchain-security/x/ccv/democracy/governance"
)

type ForbiddenProposalsDecorator struct {
	keeperMap                   map[string]interface{}
	isLegacyProposalWhitelisted func(govv1beta1.Content) bool
	isParamChangeWhitelisted    func(map[ccvgov.ParamChangeKey]struct{}) bool
	isModuleWhiteList           func(string) bool
}

func NewForbiddenProposalsDecorator(
	whiteListFn func(govv1beta1.Content) bool,
	isParamChangeWhitelisted func(map[ccvgov.ParamChangeKey]struct{}) bool,
	keeperMap map[string]interface{},
	isModuleWhiteList func(string) bool,
) ForbiddenProposalsDecorator {
	return ForbiddenProposalsDecorator{
		isLegacyProposalWhitelisted: whiteListFn,
		keeperMap:                   keeperMap,
		isParamChangeWhitelisted:    isParamChangeWhitelisted,
		isModuleWhiteList:           isModuleWhiteList,
	}
}

func (decorator ForbiddenProposalsDecorator) AnteHandle(ctx sdk.Context, tx sdk.Tx, simulate bool, next sdk.AnteHandler) (newCtx sdk.Context, err error) {
	currHeight := ctx.BlockHeight()

	for _, msg := range tx.GetMsgs() {
		submitProposalMgs, ok := msg.(*govv1.MsgSubmitProposal)
		// if the message is MsgSubmitProposal, check if proposal is whitelisted
		if ok {
			messages := submitProposalMgs.GetMessages()
			checkFlag := true

			for _, message := range messages {

				sdkMsg, ok := message.GetCachedValue().(*govv1.MsgExecLegacyContent)
				if !ok {
					if decorator.isModuleWhiteList(message.TypeUrl) {
						m := message.GetCachedValue()
						switch m := m.(type) {
						case *minttypes.MsgUpdateParams:
							if keeper, ok := decorator.keeperMap[message.TypeUrl].(mintkeeper.Keeper); ok {
								newParam := m.Params
								currentParam := keeper.GetParams(ctx)
								ccvgov.CheckIfParamKeyIsWhitelisted(&checkFlag, message.TypeUrl, currentParam, newParam, decorator.isParamChangeWhitelisted)
							} else {
								checkFlag = false
							}
						case *banktypes.MsgUpdateParams:
							if keeper, ok := decorator.keeperMap[message.TypeUrl].(bankkeeper.Keeper); ok {
								newParam := m.Params
								currentParam := keeper.GetParams(ctx)
								ccvgov.CheckIfParamKeyIsWhitelisted(&checkFlag, message.TypeUrl, currentParam, newParam, decorator.isParamChangeWhitelisted)
							} else {
								checkFlag = false
							}
						case *distrtypes.MsgUpdateParams:
							if keeper, ok := decorator.keeperMap[message.TypeUrl].(distrkeeper.Keeper); ok {
								newParam := m.Params
								currentParam := keeper.GetParams(ctx)
								ccvgov.CheckIfParamKeyIsWhitelisted(&checkFlag, message.TypeUrl, currentParam, newParam, decorator.isParamChangeWhitelisted)
							} else {
								checkFlag = false
							}
						case *stakingtypes.MsgUpdateParams:
							if keeper, ok := decorator.keeperMap[message.TypeUrl].(stakingkeeper.Keeper); ok {
								newParam := m.Params
								currentParam := keeper.GetParams(ctx)
								ccvgov.CheckIfParamKeyIsWhitelisted(&checkFlag, message.TypeUrl, currentParam, newParam, decorator.isParamChangeWhitelisted)
							} else {
								checkFlag = false
							}
						case *govv1.MsgUpdateParams:
							if keeper, ok := decorator.keeperMap[message.TypeUrl].(govkeeper.Keeper); ok {
								newParam := m.Params
								currentParam := keeper.GetParams(ctx)
								ccvgov.CheckIfParamKeyIsWhitelisted(&checkFlag, message.TypeUrl, currentParam, newParam, decorator.isParamChangeWhitelisted)
							} else {
								checkFlag = false
							}
						default:
							checkFlag = false
						}
					} else {
						checkFlag = false
					}
				} else {
					content, err := govv1.LegacyContentFromMessage(sdkMsg)
					if err != nil {
						continue
					}
					if !decorator.isLegacyProposalWhitelisted(content) {
						checkFlag = false
					}
				}
			}

			if !checkFlag {
				return ctx, fmt.Errorf("tx contains unsupported proposal message types at height %d", currHeight)
			}
		}
	}

	return next(ctx, tx, simulate)
}
