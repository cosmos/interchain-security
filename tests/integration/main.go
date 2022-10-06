package main

import (
	"bufio"
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"log"
	"os"
	"os/exec"
	"reflect"
	"sync"
	"time"

	"github.com/kylelemons/godebug/pretty"
)

var verbose = false
var localSdkPath = flag.String("local-sdk-path", "",
	"path of a local sdk version to build and reference in integration tests")

func main() {
	flag.Parse()

	// wg waits for all runners to complete
	var wg sync.WaitGroup

	start := time.Now()
	tr := DefaultTestRun()
	tr.SetLocalSDKPath(*localSdkPath)
	tr.ValidateStringLiterals()

	dmc := DemocracyTestRun()
	dmc.SetLocalSDKPath(*localSdkPath)
	dmc.ValidateStringLiterals()

	wg.Add(1)
	go tr.ExecuteSteps(&wg, "default", happyPathSteps)

	wg.Add(1)
	go dmc.ExecuteSteps(&wg, "democracy", democracySteps)

	wg.Wait()
	fmt.Printf("TOTAL TIME ELAPSED: %v\n", time.Since(start))
}

func (tr TestRun) runStep(step Step, verbose bool) {
	tr.logger.Printf("%#v\n", step.action)
	switch action := step.action.(type) {
	case StartChainAction:
		tr.startChain(action, verbose)
	case SendTokensAction:
		tr.sendTokens(action, verbose)
	case submitTextProposalAction:
		tr.submitTextProposal(action, verbose)
	case submitConsumerProposalAction:
		tr.submitConsumerAdditionProposal(action, verbose)
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
	case relayRewardPacketsToProviderAction:
		tr.relayRewardPacketsToProvider(action, verbose)
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
	case registerRepresentativeAction:
		tr.registerRepresentative(action, verbose)
	default:
		tr.logger.Fatalf(fmt.Sprintf(`unknown action: %#v`, action))
	}

	modelState := step.state
	actualState := tr.getState(step.state)

	// Check state
	if !reflect.DeepEqual(actualState, modelState) {
		pretty.Fprint(tr.logger.Writer(), "actual state", actualState)
		pretty.Fprint(tr.logger.Writer(), "model state", modelState)
		// pretty.Print("model state", modelState)
		tr.logger.Fatalf(`actual state (-) not equal to model state (+): %s` + pretty.Compare(actualState, modelState))
	}

	// pretty.Print(actualState)
	buf, _ := json.Marshal(actualState)
	tr.logger.Println(string(buf))
	// pretty.Fprint(tr.logger.Writer(), actualState)
}

// Starts docker container and sequentially runs steps
func (tr TestRun) ExecuteSteps(wg *sync.WaitGroup, name string, steps []Step) {
	defer wg.Done()

	// save logs to file
	if _, err := os.Stat("./logs"); errors.Is(err, os.ErrNotExist) {
		err := os.Mkdir("./logs", os.ModePerm)
		if !errors.Is(err, os.ErrExist) {
			panic(fmt.Sprintf("could not create log dir: %s", err))
		}
	}
	f, err := os.Create(fmt.Sprintf("./logs/%d_%s.log", time.Now().Unix(), tr.name))
	if err != nil {
		panic(fmt.Sprintf("could not create logfile: %s", err))
	}
	defer f.Close()

	tr.logger = log.New(f, "", log.Ldate|log.Ltime)

	fmt.Printf("============================================ start %s tests ============================================\n", name)

	start := time.Now()
	tr.startDocker()

	for _, step := range steps {
		tr.runStep(step, verbose)
	}

	fmt.Printf("\n\ntime elapsed for %s: %v\n", name, time.Since(start))
	fmt.Printf("============================================ end %s tests ============================================\n", name)
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
