package main

import (
	"bufio"
	"fmt"
	"log"
	"os/exec"
	"reflect"
	"time"

	"github.com/kylelemons/godebug/pretty"
)

var verbose = true

func main() {
	fmt.Println("============================================ start happy path tests ============================================")
	start := time.Now()
	tr := DefaultTestRun()
	tr.ParseCLIFlags()
	tr.ValidateStringLiterals()
	tr.startDocker()

	for _, step := range happyPathSteps {
		tr.runStep(step, verbose)
	}

	fmt.Printf("happy path tests successful - time elapsed %v\n", time.Since(start))

	fmt.Println("============================================ start democracy path tests ============================================")
	start = time.Now()
	tr.startDocker()

	for _, step := range democracySteps {
		tr.runStep(step, verbose)
	}

	fmt.Printf("democracy path tests successful - time elapsed %v\n", time.Since(start))
}

func (tr TestRun) runStep(step Step, verbose bool) {
	fmt.Printf("%#v\n", step.action)
	switch action := step.action.(type) {
	case StartChainAction:
		tr.startChain(action, verbose)
	case SendTokensAction:
		tr.sendTokens(action, verbose)
	case submitTextProposalAction:
		tr.submitTextProposal(action, verbose)
	case submitConsumerProposalAction:
		tr.submitConsumerProposal(action, verbose)
	case submitParamChangeProposalAction:
		tr.submitParamChangeProposal(action, verbose)
	case voteGovProposalAction:
		tr.voteGovProposal(action, verbose)
	case startConsumerChainAction:
		tr.startConsumerChain(action, verbose)
	case addChainToRelayerAction:
		tr.addChainToRelayer(action, verbose)
	case addIbcConnectionAction:
		tr.addIbcConnection(action, verbose)
	case addIbcChannelAction:
		tr.addIbcChannel(action, verbose)
	case transferChannelCompleteAction:
		tr.transferChannelComplete(action, verbose)
	case relayPacketsAction:
		tr.relayPackets(action, verbose)
	case delegateTokensAction:
		tr.delegateTokens(action, verbose)
	case unbondTokensAction:
		tr.unbondTokens(action, verbose)
	case redelegateTokensAction:
		tr.redelegateTokens(action, verbose)
	case downtimeSlashAction:
		tr.invokeDowntimeSlash(action, verbose)
	case unjailValidatorAction:
		tr.unjailValidator(action, verbose)
	case registerRepresentAction:
		tr.registerRepresent(action, verbose)
	default:
		log.Fatalf(fmt.Sprintf(`unknown action: %#v`, action))
	}

	modelState := step.state
	actualState := tr.getState(step.state)

	// Check state
	if !reflect.DeepEqual(actualState, modelState) {
		pretty.Print("actual state", actualState)
		pretty.Print("model state", modelState)
		log.Fatal(`actual state (-) not equal to model state (+): ` + pretty.Compare(actualState, modelState))
	}

	pretty.Print(actualState)
}

func (tr TestRun) startDocker() {
	scriptStr := "tests/integration/testnet-scripts/start-docker.sh " +
		tr.containerConfig.containerName + " " +
		tr.containerConfig.instanceName + " " +
		tr.localSdkPath

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("/bin/bash", "-c", scriptStr)

	cmdReader, err := cmd.StdoutPipe()
	if err != nil {
		log.Fatal(err)
	}
	cmd.Stderr = cmd.Stdout

	if err := cmd.Start(); err != nil {
		log.Fatal(err)
	}

	scanner := bufio.NewScanner(cmdReader)

	for scanner.Scan() {
		out := scanner.Text()
		if verbose {
			fmt.Println("startDocker: " + out)
		}
		if out == "beacon!!!!!!!!!!" {
			return
		}
	}
	if err := scanner.Err(); err != nil {
		log.Fatal(err)
	}

	err = cmd.Wait()
	log.Fatalf("StartDocker exited with error: %v", err)
}
