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
	start := time.Now()
	tr := DefaultTestRun()
	tr.ParseCLIFlags()
	tr.ValidateStringLiterals()
	tr.startDocker()

	for _, step := range happyPathSteps {
		tr.runStep(step, verbose)
	}

	fmt.Printf("test successful - time elapsed %v\n", time.Since(start))
}

func (tr TestRun) runStep(step Step, verbose bool) {
	fmt.Printf("%#v\n", step.action)
	switch action := step.action.(type) {
	case StartChainAction:
		tr.startChain(action, verbose)
	case SendTokensAction:
		tr.sendTokens(action, verbose)
	case SubmitTextProposalAction:
		tr.submitTextProposal(action, verbose)
	case SubmitConsumerProposalAction:
		tr.submitConsumerProposal(action, verbose)
	case VoteGovProposalAction:
		tr.voteGovProposal(action, verbose)
	case StartConsumerChainAction:
		tr.startConsumerChain(action, verbose)
	case AddChainToRelayerAction:
		tr.addChainToRelayer(action, verbose)
	case AddIbcConnectionAction:
		tr.addIbcConnection(action, verbose)
	case AddIbcChannelAction:
		tr.addIbcChannel(action, verbose)
	case RelayPacketsAction:
		tr.relayPackets(action, verbose)
	case DelegateTokensAction:
		tr.delegateTokens(action, verbose)
	case UnbondTokensAction:
		tr.unbondTokens(action, verbose)
	case RedelegateTokensAction:
		tr.redelegateTokens(action, verbose)
	case SlashAction:
		tr.InvokeSlash(action, verbose)
	case RestoreVotingPowerAction:
		tr.RestoreVotingPower(action, verbose)
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
	scriptStr := "integration-tests/testnet-scripts/start-docker.sh " +
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
