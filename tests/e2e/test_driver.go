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
func (pr *DefaultDriver) Run(steps []Step, target ExecutionTarget, verbose bool) error {
	pr.target = target
	pr.verbose = verbose

	fmt.Printf("=============== started %s tests ===============\n", pr.testCfg.name)

	start := time.Now()
	for i, step := range steps {
		fmt.Printf("running %s: step %d/%d == %s \n",
			pr.testCfg.name, i+1, len(steps), reflect.TypeOf(step.Action).Name())

		err := pr.runStep(step)
		if err != nil {
			return err
		}
	}
	fmt.Printf("=============== finished %s tests in %v ===============\n", pr.testCfg.name, time.Since(start))
	return nil
}

func (pr *DefaultDriver) runStep(step Step) error {
	err := pr.runAction(step.Action)
	if err != nil {
		return err
	}
	modelState := step.State
	actualState, err := pr.getState(step.State)
	if err != nil {
		return err
	}

	// Check state
	if !reflect.DeepEqual(actualState, modelState) {
		fmt.Printf("=============== %s FAILED ===============\n", pr.testCfg.name)
		fmt.Println("FAILED action", reflect.TypeOf(step.Action).Name())
		pretty.Print("actual state", actualState)
		pretty.Print("model state", modelState)
		log.Fatal(`actual state (-) not equal to model state (+): ` + pretty.Compare(actualState, modelState))
	}
	return nil
}

func (pr *DefaultDriver) GetState(modelState State) {
	pr.testCfg.getState(modelState)
}

func (pr *DefaultDriver) runAction(action interface{}) error {
	switch action := action.(type) {
	case StartChainAction:
		pr.testCfg.startChain(action, pr.target, pr.verbose)
	case StartSovereignChainAction:
		pr.testCfg.startSovereignChain(action, pr.verbose)
	case LegacyUpgradeProposalAction:
		pr.testCfg.submitLegacyUpgradeProposal(action, pr.verbose)
	case WaitUntilBlockAction:
		pr.testCfg.waitUntilBlockOnChain(action)
	case ChangeoverChainAction:
		pr.testCfg.changeoverChain(action, pr.verbose)
	case SendTokensAction:
		pr.testCfg.sendTokens(action, pr.verbose)
	case SubmitTextProposalAction:
		pr.testCfg.submitTextProposal(action, pr.verbose)
	case SubmitConsumerAdditionProposalAction:
		pr.testCfg.submitConsumerAdditionProposal(action, pr.verbose)
	case SubmitConsumerRemovalProposalAction:
		pr.testCfg.submitConsumerRemovalProposal(action, pr.verbose)
	case SubmitParamChangeLegacyProposalAction:
		pr.testCfg.submitParamChangeProposal(action, pr.verbose)
	case VoteGovProposalAction:
		pr.testCfg.voteGovProposal(action, pr.verbose)
	case StartConsumerChainAction:
		pr.testCfg.startConsumerChain(action, pr.target, pr.verbose)
	case AddChainToRelayerAction:
		pr.testCfg.addChainToRelayer(action, pr.verbose)
	case CreateIbcClientsAction:
		pr.testCfg.createIbcClientsHermes(action, pr.verbose)
	case AddIbcConnectionAction:
		pr.testCfg.addIbcConnection(action, pr.verbose)
	case AddIbcChannelAction:
		pr.testCfg.addIbcChannel(action, pr.verbose)
	case TransferChannelCompleteAction:
		pr.testCfg.transferChannelComplete(action, pr.verbose)
	case RelayPacketsAction:
		pr.testCfg.relayPackets(action, pr.verbose)
	case RelayRewardPacketsToProviderAction:
		pr.testCfg.relayRewardPacketsToProvider(action, pr.verbose)
	case DelegateTokensAction:
		pr.testCfg.delegateTokens(action, pr.verbose)
	case UnbondTokensAction:
		pr.testCfg.unbondTokens(action, pr.verbose)
	case CancelUnbondTokensAction:
		pr.testCfg.cancelUnbondTokens(action, pr.verbose)
	case RedelegateTokensAction:
		pr.testCfg.redelegateTokens(action, pr.verbose)
	case DowntimeSlashAction:
		pr.testCfg.invokeDowntimeSlash(action, pr.verbose)
	case UnjailValidatorAction:
		pr.testCfg.unjailValidator(action, pr.verbose)
	case DoublesignSlashAction:
		pr.testCfg.invokeDoublesignSlash(action, pr.verbose)
	case LightClientAmnesiaAttackAction:
		pr.testCfg.lightClientAmnesiaAttack(action, pr.verbose)
	case LightClientEquivocationAttackAction:
		pr.testCfg.lightClientEquivocationAttack(action, pr.verbose)
	case LightClientLunaticAttackAction:
		pr.testCfg.lightClientLunaticAttack(action, pr.verbose)
	case RegisterRepresentativeAction:
		pr.testCfg.registerRepresentative(action, pr.verbose)
	case AssignConsumerPubKeyAction:
		pr.testCfg.assignConsumerPubKey(action, pr.verbose)
	case SlashMeterReplenishmentAction:
		pr.testCfg.waitForSlashMeterReplenishment(action, pr.verbose)
	case WaitTimeAction:
		pr.testCfg.waitForTime(action, pr.verbose)
	case StartRelayerAction:
		pr.testCfg.startRelayer(action, pr.verbose)
	case ForkConsumerChainAction:
		pr.testCfg.forkConsumerChain(action, pr.verbose)
	case UpdateLightClientAction:
		pr.testCfg.updateLightClient(action, pr.verbose)
	case StartConsumerEvidenceDetectorAction:
		pr.testCfg.startConsumerEvidenceDetector(action, pr.verbose)
	case SubmitChangeRewardDenomsProposalAction:
		pr.testCfg.submitChangeRewardDenomsProposal(action, pr.verbose)
	default:
		log.Fatalf("unknown action in testRun %s: %#v", pr.testCfg.name, action)
	}
	return nil
}

func (pr *DefaultDriver) getState(modelState State) (State, error) {
	// forwarding it for now
	return pr.testCfg.getState(modelState), nil
}
