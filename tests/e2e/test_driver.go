package main

import (
	"fmt"
	"log"
	"reflect"

	clienttypes "github.com/cosmos/ibc-go/v7/modules/core/02-client/types"
	"github.com/kylelemons/godebug/pretty"
)

// TestCaseDriver knows how different TC can be executed
type TestCaseDriver interface {
	Run(steps []Step, target ExecutionTarget, verbose bool) error
}

func GetTestCaseDriver(testCfg TestConfig) TestCaseDriver {
	return &DefaultDriver{testCfg: testCfg}
}

type DefaultDriver struct {
	testCfg TestConfig
	target  ExecutionTarget
	verbose bool
}

// Execute tests
func (td *DefaultDriver) Run(steps []Step, target ExecutionTarget, verbose bool) error {
	td.target = target
	td.verbose = verbose

	for i, step := range steps {
		fmt.Printf("running %s: step %d/%d == %s \n",
			td.testCfg.name, i+1, len(steps), reflect.TypeOf(step.Action).Name())

		err := td.runStep(step)
		if err != nil {
			return err
		}
	}
	return nil
}

// runStep executes an action and evaluates the result against expected state
func (td *DefaultDriver) runStep(step Step) error {
	err := td.runAction(step.Action)
	if err != nil {
		return err
	}
	modelState := step.State
	actualState := td.getState(modelState)

	// Check state
	if !reflect.DeepEqual(actualState, modelState) {
		fmt.Printf("=============== %s FAILED ===============\n", td.testCfg.name)
		fmt.Println("FAILED action", reflect.TypeOf(step.Action).Name())
		pretty.Print("actual state", actualState)
		pretty.Print("model state", modelState)
		log.Fatal(`actual state (-) not equal to model state (+): ` + pretty.Compare(actualState, modelState))
	}
	return nil
}

type Target interface {
	GetChainState(chain ChainID, modelState ChainState) ChainState
	GetBalances(chain ChainID, modelState map[ValidatorID]uint) map[ValidatorID]uint
	GetProposals(chain ChainID, modelState map[uint]Proposal) map[uint]Proposal
	GetValPowers(chain ChainID, modelState map[ValidatorID]uint) map[ValidatorID]uint
	GetParams(chain ChainID, modelState []Param) []Param
	GetRewards(chain ChainID, modelState Rewards) Rewards
	GetStakedTokens(chain ChainID, modelState map[ValidatorID]uint) map[ValidatorID]uint
	GetConsumerAddresses(chain ChainID, modelState map[ValidatorID]string) map[ValidatorID]string
	GetProviderAddresses(chain ChainID, modelState map[ValidatorID]string) map[ValidatorID]string
	GetRegisteredConsumerRewardDenoms(chain ChainID) []string
	GetClientFrozenHeight(chain ChainID, clientID string) clienttypes.Height
}

func (td *DefaultDriver) getTargetDriver(chainID ChainID) (Target, error) {
	target := Chain{target: td.target,
		testConfig: td.testCfg,
	}

	return target, nil
}

func (td *DefaultDriver) getState(modelState State) State {
	systemState := State{}
	for chainID, modelState := range modelState {
		target, err := td.getTargetDriver(chainID)
		if err != nil {
			log.Panicln("no target driver found for chain ", chainID)
		}

		if td.verbose {
			fmt.Println("Getting model state for chain: ", chainID)
		}
		systemState[chainID] = target.GetChainState(chainID, modelState)
	}

	return systemState
}

func (td *DefaultDriver) runAction(action interface{}) error {
	target := Chain{target: td.target, testConfig: td.testCfg}
	switch action := action.(type) {
	case StartChainAction:
		target.startChain(action, td.verbose)
	case StartSovereignChainAction:
		target.startSovereignChain(action, td.verbose)
	case LegacyUpgradeProposalAction:
		target.submitLegacyUpgradeProposal(action, td.verbose)
	case WaitUntilBlockAction:
		target.waitUntilBlockOnChain(action)
	case ChangeoverChainAction:
		target.changeoverChain(action, td.verbose)
	case SendTokensAction:
		target.sendTokens(action, td.verbose)
	case SubmitTextProposalAction:
		target.submitTextProposal(action, td.verbose)
	case SubmitConsumerAdditionProposalAction:
		target.submitConsumerAdditionProposal(action, td.verbose)
	case SubmitConsumerRemovalProposalAction:
		target.submitConsumerRemovalProposal(action, td.verbose)
	case SubmitEnableTransfersProposalAction:
		target.submitEnableTransfersProposalAction(action, td.verbose)
	case VoteGovProposalAction:
		target.voteGovProposal(action, td.verbose)
	case StartConsumerChainAction:
		target.startConsumerChain(action, td.verbose)
	case AddChainToRelayerAction:
		target.addChainToRelayer(action, td.verbose)
	case CreateIbcClientsAction:
		target.createIbcClientsHermes(action, td.verbose)
	case AddIbcConnectionAction:
		target.addIbcConnection(action, td.verbose)
	case AddIbcChannelAction:
		target.addIbcChannel(action, td.verbose)
	case TransferChannelCompleteAction:
		target.transferChannelComplete(action, td.verbose)
	case RelayPacketsAction:
		target.relayPackets(action, td.verbose)
	case RelayRewardPacketsToProviderAction:
		target.relayRewardPacketsToProvider(action, td.verbose)
	case DelegateTokensAction:
		target.delegateTokens(action, td.verbose)
	case UnbondTokensAction:
		target.unbondTokens(action, td.verbose)
	case CancelUnbondTokensAction:
		target.cancelUnbondTokens(action, td.verbose)
	case RedelegateTokensAction:
		target.redelegateTokens(action, td.verbose)
	case DowntimeSlashAction:
		target.invokeDowntimeSlash(action, td.verbose)
	case UnjailValidatorAction:
		target.unjailValidator(action, td.verbose)
	case DoublesignSlashAction:
		target.invokeDoublesignSlash(action, td.verbose)
	case LightClientAmnesiaAttackAction:
		target.lightClientAmnesiaAttack(action, td.verbose)
	case LightClientEquivocationAttackAction:
		target.lightClientEquivocationAttack(action, td.verbose)
	case LightClientLunaticAttackAction:
		target.lightClientLunaticAttack(action, td.verbose)
	case RegisterRepresentativeAction:
		target.registerRepresentative(action, td.verbose)
	case AssignConsumerPubKeyAction:
		target.assignConsumerPubKey(action, td.verbose)
	case SlashMeterReplenishmentAction:
		target.waitForSlashMeterReplenishment(action, td.verbose)
	case WaitTimeAction:
		target.waitForTime(action, td.verbose)
	case StartRelayerAction:
		target.startRelayer(action, td.verbose)
	case ForkConsumerChainAction:
		target.forkConsumerChain(action, td.verbose)
	case UpdateLightClientAction:
		target.updateLightClient(action, td.verbose)
	case StartConsumerEvidenceDetectorAction:
		target.startConsumerEvidenceDetector(action, td.verbose)
	case SubmitChangeRewardDenomsProposalAction:
		target.submitChangeRewardDenomsProposal(action, td.verbose)
	default:
		log.Fatalf("unknown action in testRun %s: %#v", td.testCfg.name, action)
	}
	return nil
}
