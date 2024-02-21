package main

import (
	"fmt"
	"log"
	"reflect"
	"time"

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

	fmt.Printf("=============== started %s tests ===============\n", td.testCfg.name)

	start := time.Now()
	for i, step := range steps {
		fmt.Printf("running %s: step %d/%d == %s \n",
			td.testCfg.name, i+1, len(steps), reflect.TypeOf(step.Action).Name())

		err := td.runStep(step)
		if err != nil {
			return err
		}
	}
	fmt.Printf("=============== finished %s tests in %v ===============\n", td.testCfg.name, time.Since(start))
	return nil
}

// runStep executes an action and evaluates the result against expected state
func (td *DefaultDriver) runStep(step Step) error {
	err := td.runAction(step.Action)
	if err != nil {
		return err
	}
	modelState := step.State
	actualState := td.testCfg.getState(modelState, td.verbose)

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

func (td *DefaultDriver) runAction(action interface{}) error {
	switch action := action.(type) {
	case StartChainAction:
		td.testCfg.startChain(action, td.target, td.verbose)
	case StartSovereignChainAction:
		td.testCfg.startSovereignChain(action, td.target, td.verbose)
	case LegacyUpgradeProposalAction:
		td.testCfg.submitLegacyUpgradeProposal(action, td.target, td.verbose)
	case WaitUntilBlockAction:
		td.testCfg.waitUntilBlockOnChain(action)
	case ChangeoverChainAction:
		td.testCfg.changeoverChain(action, td.target, td.verbose)
	case SendTokensAction:
		td.testCfg.sendTokens(action, td.target, td.verbose)
	case SubmitTextProposalAction:
		td.testCfg.submitTextProposal(action, td.target, td.verbose)
	case SubmitConsumerAdditionProposalAction:
		td.testCfg.submitConsumerAdditionProposal(action, td.target, td.verbose)
	case SubmitConsumerRemovalProposalAction:
		td.testCfg.submitConsumerRemovalProposal(action, td.target, td.verbose)
	case SubmitParamChangeLegacyProposalAction:
		td.testCfg.submitParamChangeProposal(action, td.target, td.verbose)
	case VoteGovProposalAction:
		td.testCfg.voteGovProposal(action, td.target, td.verbose)
	case StartConsumerChainAction:
		td.testCfg.startConsumerChain(action, td.target, td.verbose)
	case AddChainToRelayerAction:
		td.testCfg.addChainToRelayer(action, td.target, td.verbose)
	case CreateIbcClientsAction:
		td.testCfg.createIbcClientsHermes(action, td.target, td.verbose)
	case AddIbcConnectionAction:
		td.testCfg.addIbcConnection(action, td.target, td.verbose)
	case AddIbcChannelAction:
		td.testCfg.addIbcChannel(action, td.target, td.verbose)
	case TransferChannelCompleteAction:
		td.testCfg.transferChannelComplete(action, td.target, td.verbose)
	case RelayPacketsAction:
		td.testCfg.relayPackets(action, td.target, td.verbose)
	case RelayRewardPacketsToProviderAction:
		td.testCfg.relayRewardPacketsToProvider(action, td.target, td.verbose)
	case DelegateTokensAction:
		td.testCfg.delegateTokens(action, td.target, td.verbose)
	case UnbondTokensAction:
		td.testCfg.unbondTokens(action, td.target, td.verbose)
	case CancelUnbondTokensAction:
		td.testCfg.cancelUnbondTokens(action, td.target, td.verbose)
	case RedelegateTokensAction:
		td.testCfg.redelegateTokens(action, td.target, td.verbose)
	case DowntimeSlashAction:
		td.testCfg.invokeDowntimeSlash(action, td.target, td.verbose)
	case UnjailValidatorAction:
		td.testCfg.unjailValidator(action, td.target, td.verbose)
	case DoublesignSlashAction:
		td.testCfg.invokeDoublesignSlash(action, td.target, td.verbose)
	case LightClientAmnesiaAttackAction:
		td.testCfg.lightClientAmnesiaAttack(action, td.verbose)
	case LightClientEquivocationAttackAction:
		td.testCfg.lightClientEquivocationAttack(action, td.verbose)
	case LightClientLunaticAttackAction:
		td.testCfg.lightClientLunaticAttack(action, td.verbose)
	case RegisterRepresentativeAction:
		td.testCfg.registerRepresentative(action, td.target, td.verbose)
	case AssignConsumerPubKeyAction:
		td.testCfg.assignConsumerPubKey(action, td.target, td.verbose)
	case SlashMeterReplenishmentAction:
		td.testCfg.waitForSlashMeterReplenishment(action, td.verbose)
	case WaitTimeAction:
		td.testCfg.waitForTime(action, td.verbose)
	case StartRelayerAction:
		td.testCfg.startRelayer(action, td.target, td.verbose)
	case ForkConsumerChainAction:
		td.testCfg.forkConsumerChain(action, td.verbose)
	case UpdateLightClientAction:
		td.testCfg.updateLightClient(action, td.verbose)
	case StartConsumerEvidenceDetectorAction:
		td.testCfg.startConsumerEvidenceDetector(action, td.target, td.verbose)
	case SubmitChangeRewardDenomsProposalAction:
		td.testCfg.submitChangeRewardDenomsProposal(action, td.target, td.verbose)
	default:
		log.Fatalf("unknown action in testRun %s: %#v", td.testCfg.name, action)
	}
	return nil
}
