package main

import (
	"fmt"
	"log"
	"reflect"
	"time"

	"github.com/kylelemons/godebug/pretty"
	"golang.org/x/mod/semver"

	clienttypes "github.com/cosmos/ibc-go/v8/modules/core/02-client/types"
	e2e "github.com/cosmos/interchain-security/v6/tests/e2e/testlib"
	v4 "github.com/cosmos/interchain-security/v6/tests/e2e/v4"
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
		testConfig: &td.testCfg,
	}
	icsVersion := td.getIcsVersion(chainID)
	switch icsVersion {
	case "v3", "v4":
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
			containerConfig:  &td.testCfg.containerConfig,
			validatorConfigs: td.testCfg.validatorConfigs,
			chainConfigs:     td.testCfg.chainConfigs,
			target:           td.target,
		}
		if td.verbose {
			fmt.Println("Using default driver for version", icsVersion, " for chain ", chainID)
		}
	}

	return target
}

func (td *DefaultDriver) getState(modelState State) State {
	systemState := State{}
	for chainID, modelState := range modelState {
		if td.verbose {
			fmt.Println("Getting model state for chain: ", chainID)
		}
		systemState[chainID] = td.GetChainState(chainID, modelState)
	}

	return systemState
}

func (td *DefaultDriver) GetChainState(chain ChainID, modelState ChainState) e2e.ChainState {
	chainState := ChainState{}
	chainDriver := td.getTargetDriver(chain)
	// providerDriver is the target driver for the provider chain
	providerDriver := td.getTargetDriver("provi")

	if modelState.ValBalances != nil {
		valBalances := chainDriver.GetBalances(chain, *modelState.ValBalances)
		chainState.ValBalances = &valBalances
	}

	if modelState.Proposals != nil {
		proposals := chainDriver.GetProposals(chain, *modelState.Proposals)
		chainState.Proposals = &proposals
	}

	if modelState.ProposedConsumerChains != nil {
		proposedConsumerChains := chainDriver.GetProposedConsumerChains(chain)
		chainState.ProposedConsumerChains = &proposedConsumerChains
	}

	if modelState.ValPowers != nil {
		chainDriver.waitBlocks(chain, 1, 10*time.Second)
		powers := chainDriver.GetValPowers(chain, *modelState.ValPowers)
		chainState.ValPowers = &powers
	}

	if modelState.StakedTokens != nil {
		representPowers := chainDriver.GetStakedTokens(chain, *modelState.StakedTokens)
		chainState.StakedTokens = &representPowers
	}

	if modelState.IBCTransferParams != nil {
		params := chainDriver.target.GetIBCTransferParams(chain)
		chainState.IBCTransferParams = &params
	}

	if modelState.Rewards != nil {
		rewards := chainDriver.GetRewards(chain, *modelState.Rewards)
		chainState.Rewards = &rewards
	}

	if modelState.ConsumerChains != nil {
		chains := chainDriver.target.GetConsumerChains(chain)
		chainState.ConsumerChains = &chains
	}

	if modelState.AssignedKeys != nil {
		assignedKeys := providerDriver.GetConsumerAddresses(chain, *modelState.AssignedKeys)
		chainState.AssignedKeys = &assignedKeys
	}

	if modelState.ProviderKeys != nil {
		providerKeys := providerDriver.GetProviderAddresses(chain, *modelState.ProviderKeys)
		chainState.ProviderKeys = &providerKeys
	}

	if modelState.RegisteredConsumerRewardDenoms != nil {
		registeredConsumerRewardDenoms := chainDriver.target.GetRegisteredConsumerRewardDenoms(chain)
		chainState.RegisteredConsumerRewardDenoms = &registeredConsumerRewardDenoms
	}

	if modelState.ClientsFrozenHeights != nil {
		chainClientsFrozenHeights := map[string]clienttypes.Height{}
		for id := range *modelState.ClientsFrozenHeights {
			chainClientsFrozenHeights[id] = providerDriver.GetClientFrozenHeight(chain, id)
		}
		chainState.ClientsFrozenHeights = &chainClientsFrozenHeights
	}

	if modelState.HasToValidate != nil {
		hasToValidate := map[ValidatorID][]ChainID{}
		for validatorId := range *modelState.HasToValidate {
			hasToValidate[validatorId] = providerDriver.target.GetHasToValidate(validatorId)
		}
		chainState.HasToValidate = &hasToValidate
	}

	if modelState.InflationRateChange != nil {
		// get the inflation rate now
		inflationRateNow := chainDriver.target.GetInflationRate(chain)

		// wait a block
		chainDriver.waitBlocks(chain, 1, 10*time.Second)

		// get the new inflation rate
		inflationRateAfter := chainDriver.target.GetInflationRate(chain)

		// calculate the change
		inflationRateChange := inflationRateAfter - inflationRateNow
		var inflationRateChangeDirection int
		if inflationRateChange > 0 {
			inflationRateChangeDirection = 1
		} else if inflationRateChange < 0 {
			inflationRateChangeDirection = -1
		} else {
			inflationRateChangeDirection = 0
		}
		chainState.InflationRateChange = &inflationRateChangeDirection
	}

	if modelState.ConsumerCommissionRates != nil {
		consumerCommissionRates := providerDriver.GetConsumerCommissionRates(chain, *modelState.ConsumerCommissionRates)
		chainState.ConsumerCommissionRates = &consumerCommissionRates
	}

	if modelState.ConsumerPendingPacketQueueSize != nil {
		pendingPacketQueueSize := chainDriver.target.GetPendingPacketQueueSize(chain)
		chainState.ConsumerPendingPacketQueueSize = &pendingPacketQueueSize
	}

	if *verbose {
		log.Println("Done getting chain state:\n" + pretty.Sprint(chainState))
	}

	return chainState
}

func (td *DefaultDriver) runAction(action interface{}) error {
	switch action := action.(type) {
	case StartChainAction:
		target := td.getTargetDriver(action.Chain)
		target.startChain(action, td.verbose)
	case StartSovereignChainAction:
		target := td.getTargetDriver(action.Chain)
		target.startSovereignChain(action, td.verbose)
	case UpgradeProposalAction:
		target := td.getTargetDriver(ChainID("sover"))
		target.submitUpgradeProposal(action, td.verbose)
	case WaitUntilBlockAction:
		target := td.getTargetDriver(action.Chain)
		target.waitUntilBlockOnChain(action)
	case ChangeoverChainAction:
		target := td.getTargetDriver("")
		target.changeoverChain(action, td.verbose)
	case SendTokensAction:
		target := td.getTargetDriver(action.Chain)
		target.sendTokens(action, td.verbose)
	case SubmitTextProposalAction:
		target := td.getTargetDriver(action.Chain)
		target.submitTextProposal(action, td.verbose)
	case SubmitConsumerAdditionProposalAction:
		target := td.getTargetDriver(action.Chain)
		version := target.testConfig.providerVersion
		if semver.IsValid(version) && semver.Compare(semver.Major(version), "v5") < 0 {
			target.submitConsumerAdditionLegacyProposal(action, td.verbose)
		} else {
			target.submitConsumerAdditionProposal(action, td.verbose)
		}
	case SubmitConsumerRemovalProposalAction:
		target := td.getTargetDriver(action.Chain)
		version := target.testConfig.providerVersion
		target = td.getTargetDriver(action.Chain)
		if semver.IsValid(version) && semver.Compare(semver.Major(version), "v5") < 0 {
			target.submitConsumerRemovalLegacyProposal(action, td.verbose)
		} else {
			target.submitConsumerRemovalProposal(action, td.verbose)
		}
	case SubmitEnableTransfersProposalAction:
		target := td.getTargetDriver(action.Chain)
		target.submitEnableTransfersProposalAction(action, td.verbose)
	case SubmitConsumerModificationProposalAction:
		target := td.getTargetDriver(action.Chain)
		version := target.testConfig.providerVersion
		if semver.IsValid(version) && semver.Compare(semver.Major(version), "v5") < 0 {
			target.submitConsumerModificationLegacyProposal(action, td.verbose)
		} else {
			target.submitConsumerModificationProposal(action, td.verbose)
		}
	case VoteGovProposalAction:
		target := td.getTargetDriver(action.Chain)
		target.voteGovProposal(action, td.verbose)
	case StartConsumerChainAction:
		target := td.getTargetDriver(action.ProviderChain)
		target.startConsumerChain(action, td.verbose)
	case AddChainToRelayerAction:
		target := td.getTargetDriver(action.Chain)
		target.addChainToRelayer(action, td.verbose)
	case CreateIbcClientsAction:
		// use default for hermes actions
		target := td.getTargetDriver("")
		target.createIbcClientsHermes(action, td.verbose)
	case AddIbcConnectionAction:
		// use default for hermes actions
		target := td.getTargetDriver("")
		target.addIbcConnection(action, td.verbose)
	case AddIbcChannelAction:
		// use default for hermes actions
		target := td.getTargetDriver("")
		target.addIbcChannel(action, td.verbose)
	case TransferChannelCompleteAction:
		// use default for hermes actions
		target := td.getTargetDriver("")
		target.transferChannelComplete(action, td.verbose)
	case RelayPacketsAction:
		// use default for hermes actions
		target := td.getTargetDriver("")
		target.relayPackets(action, td.verbose)
	case RelayRewardPacketsToProviderAction:
		// use default for hermes actions
		target := td.getTargetDriver("")
		target.relayRewardPacketsToProvider(action, td.verbose)
	case DelegateTokensAction:
		target := td.getTargetDriver(action.Chain)
		target.delegateTokens(action, td.verbose)
	case UnbondTokensAction:
		target := td.getTargetDriver(action.Chain)
		target.unbondTokens(action, td.verbose)
	case CancelUnbondTokensAction:
		target := td.getTargetDriver(action.Chain)
		target.cancelUnbondTokens(action, td.verbose)
	case RedelegateTokensAction:
		target := td.getTargetDriver(action.Chain)
		target.redelegateTokens(action, td.verbose)
	case DowntimeSlashAction:
		target := td.getTargetDriver(action.Chain)
		target.invokeDowntimeSlash(action, td.verbose)
	case UnjailValidatorAction:
		target := td.getTargetDriver(action.Provider)
		target.unjailValidator(action, td.verbose)
	case DoublesignSlashAction:
		target := td.getTargetDriver(action.Chain)
		target.invokeDoublesignSlash(action, td.verbose)
	case LightClientAmnesiaAttackAction:
		target := td.getTargetDriver(action.Chain)
		target.lightClientAmnesiaAttack(action, td.verbose)
	case LightClientEquivocationAttackAction:
		target := td.getTargetDriver(action.Chain)
		target.lightClientEquivocationAttack(action, td.verbose)
	case LightClientLunaticAttackAction:
		target := td.getTargetDriver(action.Chain)
		target.lightClientLunaticAttack(action, td.verbose)
	case RegisterRepresentativeAction:
		target := td.getTargetDriver(action.Chain)
		target.registerRepresentative(action, td.verbose)
	case e2e.AssignConsumerPubKeyAction:
		target := td.getTargetDriver(ChainID("provi"))
		target.assignConsumerPubKey(action, td.verbose)
	case SlashMeterReplenishmentAction:
		target := td.getTargetDriver(ChainID("provi"))
		target.waitForSlashMeterReplenishment(action, td.verbose)
	case WaitTimeAction:
		target := td.getTargetDriver("")
		target.waitForTime(action, td.verbose)
	case StartRelayerAction:
		target := td.getTargetDriver("")
		target.startRelayer(action, td.verbose)
	case ForkConsumerChainAction:
		target := td.getTargetDriver("")
		target.forkConsumerChain(action, td.verbose)
	case UpdateLightClientAction:
		target := td.getTargetDriver("")
		target.updateLightClient(action, td.verbose)
	case DetectorConsumerEvidenceAction:
		target := td.getTargetDriver("")
		target.detectConsumerEvidence(action, false, td.verbose)
	case SubmitChangeRewardDenomsProposalAction:
		target := td.getTargetDriver(action.Chain)
		version := target.testConfig.providerVersion
		if semver.IsValid(version) && semver.Compare(semver.Major(version), "v5") < 0 {
			target.submitChangeRewardDenomsLegacyProposal(action, td.verbose)
		} else {
			target.submitChangeRewardDenomsProposal(action, td.verbose)
		}
	case CreateConsumerChainAction:
		target := td.getTargetDriver(action.Chain)
		target.createConsumerChain(action, td.verbose)
	case UpdateConsumerChainAction:
		target := td.getTargetDriver(action.Chain)
		target.updateConsumerChain(action, td.verbose)
	case OptInAction:
		target := td.getTargetDriver("provider")
		target.optIn(action, td.verbose)
	case OptOutAction:
		target := td.getTargetDriver("provider")
		target.optOut(action, td.verbose)
	case SetConsumerCommissionRateAction:
		target := td.getTargetDriver("provider")
		target.setConsumerCommissionRate(action, td.verbose)
	case SubmitConsumerMisbehaviourAction:
		target := td.getTargetDriver("provider")
		target.submitConsumerMisbehaviour(action, td.verbose)
	default:
		log.Fatalf("unknown action in testRun %s: %#v", td.testCfg.name, action)
	}
	return nil
}
