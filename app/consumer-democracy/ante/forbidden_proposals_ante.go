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
			var checkFlag bool = true

			for _, message := range messages {
				//Check if msg is Legacy paramchange proposal
				sdkMsg, ok := message.GetCachedValue().(*govv1.MsgExecLegacyContent)
				if !ok {
					fmt.Println(message.TypeUrl)
					if decorator.isModuleWhiteList(message.TypeUrl) {
						m := message.GetCachedValue()
						switch m.(type) {
						case *minttypes.MsgUpdateParams:
							newParam := m.(*minttypes.MsgUpdateParams).Params
							keeper := decorator.keeperMap[message.TypeUrl]
							currentParam := keeper.(mintkeeper.Keeper).GetParams(ctx)
							ccvgov.CheckIfParamKeyIsWhitelisted(&checkFlag, message.TypeUrl, currentParam, newParam, decorator.isParamChangeWhitelisted)
						case *banktypes.MsgUpdateParams:
							newParam := m.(*banktypes.MsgUpdateParams).Params
							keeper := decorator.keeperMap[message.TypeUrl]
							currentParam := keeper.(bankkeeper.Keeper).GetParams(ctx)
							ccvgov.CheckIfParamKeyIsWhitelisted(&checkFlag, message.TypeUrl, currentParam, newParam, decorator.isParamChangeWhitelisted)
						case *distrtypes.MsgUpdateParams:
							newParam := m.(*distrtypes.MsgUpdateParams).Params
							keeper := decorator.keeperMap[message.TypeUrl]
							currentParam := keeper.(distrkeeper.Keeper).GetParams(ctx)
							ccvgov.CheckIfParamKeyIsWhitelisted(&checkFlag, message.TypeUrl, currentParam, newParam, decorator.isParamChangeWhitelisted)
						case *stakingtypes.MsgUpdateParams:
							newParam := m.(*stakingtypes.MsgUpdateParams).Params
							keeper := decorator.keeperMap[message.TypeUrl]
							currentParam := keeper.(stakingkeeper.Keeper).GetParams(ctx)
							ccvgov.CheckIfParamKeyIsWhitelisted(&checkFlag, message.TypeUrl, currentParam, newParam, decorator.isParamChangeWhitelisted)
						case *govv1.MsgUpdateParams:
							newParam := m.(*govv1.MsgUpdateParams).Params
							keeper := decorator.keeperMap[message.TypeUrl]
							currentParam := keeper.(govkeeper.Keeper).GetParams(ctx)
							ccvgov.CheckIfParamKeyIsWhitelisted(&checkFlag, message.TypeUrl, currentParam, newParam, decorator.isParamChangeWhitelisted)
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
