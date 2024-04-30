package main

import (
	"fmt"
	"log"
	"reflect"

	v4 "github.com/cosmos/interchain-security/v5/tests/e2e/v4"
	"github.com/kylelemons/godebug/pretty"
	"golang.org/x/mod/semver"
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

func (td *DefaultDriver) getIcsVersion(chainID ChainID) string {
	version := ""
	if td.testCfg.chainConfigs[chainID].BinaryName == "interchain-security-pd" {
		version = td.testCfg.providerVersion
	} else {
		version = td.testCfg.consumerVersion
	}
	ics := getIcsVersion(version)
	if !semver.IsValid(ics) {
		return ""
	} else {
		return semver.Major(ics)
	}
}

func (td *DefaultDriver) getTargetDriver(chainID ChainID) Chain {
	target := Chain{
		testConfig: td.testCfg,
	}
	icsVersion := td.getIcsVersion(chainID)
	switch icsVersion {
	case "v4":
		if td.verbose {
			fmt.Println("Using 'v4' driver for chain ", chainID)
		}
		target.target = v4.Commands{
			ContainerConfig:  td.testCfg.containerConfig,
			ValidatorConfigs: td.testCfg.validatorConfigs,
			ChainConfigs:     td.testCfg.chainConfigs,
			Target:           td.target,
		}
	default:
		target.target = Commands{
			containerConfig:  td.testCfg.containerConfig,
			validatorConfigs: td.testCfg.validatorConfigs,
			chainConfigs:     td.testCfg.chainConfigs,
			target:           td.target,
		}
		if td.verbose {
			fmt.Println("Using default driver ", icsVersion, " for chain ", chainID)
		}
	}

	return target
}

func (td *DefaultDriver) getState(modelState State) State {
	systemState := State{}
	for chainID, modelState := range modelState {
		target := td.getTargetDriver(chainID)

		if td.verbose {
			fmt.Println("Getting model state for chain: ", chainID)
		}
		systemState[chainID] = target.GetChainState(chainID, modelState)
	}

	return systemState
}

func (td *DefaultDriver) runAction(action interface{}) error {
	target := td.getTargetDriver("")
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
