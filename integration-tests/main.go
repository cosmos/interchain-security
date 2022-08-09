package main

import (
	"bufio"
	"fmt"
	"log"
	"os/exec"
	"reflect"

	"github.com/kylelemons/godebug/pretty"
)

var verbose = true

func main() {
	s := DefaultSystemConfig()

	s.startDocker()

	for _, step := range happyPathSteps {
		s.runStep(step, verbose)
	}

	println("test successful")
}

func (s System) runStep(step Step, verbose bool) {
	fmt.Printf("%#v\n", step.action)
	switch action := step.action.(type) {
	case StartChainAction:
		s.startChain(action, verbose)
	case SendTokensAction:
		s.sendTokens(action, verbose)
	case SubmitTextProposalAction:
		s.submitTextProposal(action, verbose)
	case SubmitConsumerProposalAction:
		s.submitConsumerProposal(action, verbose)
	case VoteGovProposalAction:
		s.voteGovProposal(action, verbose)
	case StartConsumerChainAction:
		s.startConsumerChain(action, verbose)
	case AddChainToRelayerAction:
		s.addChainToRelayer(action, verbose)
	case AddIbcConnectionAction:
		s.addIbcConnection(action, verbose)
	case AddIbcChannelAction:
		s.addIbcChannel(action, verbose)
	case RelayPacketsAction:
		s.relayPackets(action, verbose)
	case DelegateTokensAction:
		s.delegateTokens(action, verbose)
	default:
		log.Fatalf(fmt.Sprintf(`unknown action: %#v`, action))
	}

	modelState := step.state
	actualState := s.getState(step.state)

	// Check state
	if !reflect.DeepEqual(actualState, modelState) {
		pretty.Print("actual state", actualState)
		pretty.Print("model state", modelState)
		log.Fatal(`actual state (-) not equal to model state (+): ` + pretty.Compare(actualState, modelState))
	}

	pretty.Print(actualState)
}

var startDockerScript = `#!/bin/bash
# If -e is not set then if the build fails, it will use the old container, resulting in a very confusing debugging situation
# Setting -e makes it error out if the build fails
set -eux 

CONTAINER_NAME=%s
INSTANCE_NAME=%s

# Remove existing container instance
set +e
docker rm -f "$INSTANCE_NAME"
set -e

# Build the Docker container
docker build -t "$CONTAINER_NAME" .

# Run new test container instance
docker run --name "$INSTANCE_NAME" --cap-add=NET_ADMIN "$CONTAINER_NAME" /bin/bash /testnet-scripts/beacon.sh
`

func (s System) startDocker() {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("/bin/bash", "-c", fmt.Sprintf(startDockerScript, s.containerConfig.containerName, s.containerConfig.instanceName))

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
