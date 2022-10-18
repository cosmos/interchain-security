package main

import (
	"bufio"
	"flag"
	"fmt"
	"log"
	"os/exec"
	"path"
	"reflect"
	"sync"
	"time"

	"github.com/kylelemons/godebug/pretty"
)

var (
	verbose      = flag.Bool("verbose", false, "turn verbose logging on/off")
	localSdkPath = flag.String("local-sdk-path", "",
		"path of a local sdk version to build and reference in integration tests")
	providerDirLoc = flag.String("provider-dir-loc", "",
		"location to the provider directory with makefile included")
	consumerDirLoc = flag.String("consumer-dir-loc", "",
		"location to the consumer directory with makefile included")
	provBinName = flag.String("prov-bin-name", "interchain-security-pd",
		"name of provider binary")
	consBinName = flag.String("cons-bin-name", "interchain-security-cd",
		"name of consumer binary")
	democracyConsBinName = flag.String("democ-bin-name", "interchain-security-cdd",
		"name of democracy consumer binary, leave blank to skip these tests")
)

// runs integration tests
// all docker containers are built sequentially to avoid race conditions when using local cosmos-sdk
// after building docker containers, all tests are run in parallel using their respective docker containers
func main() {
	flag.Parse()
	binConfig := getBinConfigFromFlags()
	copySourceCode(*providerDirLoc, binConfig.provBinName)
	copySourceCode(*consumerDirLoc, binConfig.consBinName)

	// wg waits for all runners to complete
	var wg sync.WaitGroup

	start := time.Now()

	tr := DefaultTestRun(binConfig)
	tr.SetLocalSDKPath(*localSdkPath)
	tr.ValidateStringLiterals()
	tr.startDocker(binConfig)

	wg.Add(1)
	go tr.ExecuteSteps(&wg, happyPathSteps)

	if binConfig.democracyConsBinName == "" {
		fmt.Println("Democracy consumer tests will be skipped!")
	} else {
		dmc := DemocracyTestRun(binConfig)
		dmc.SetLocalSDKPath(*localSdkPath)
		dmc.ValidateStringLiterals()
		dmc.startDocker(binConfig)

		wg.Add(1)
		go dmc.ExecuteSteps(&wg, democracySteps)
	}

	wg.Wait()
	fmt.Printf("TOTAL TIME ELAPSED: %v\n", time.Since(start))
}

func (tr *TestRun) runStep(step Step, verbose bool) {
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
		log.Fatalf(fmt.Sprintf(`unknown action in testRun %s: %#v`, tr.name, action))
	}

	modelState := step.state
	actualState := tr.getState(step.state)

	// Check state
	if !reflect.DeepEqual(actualState, modelState) {
		pretty.Print("actual state", actualState)
		pretty.Print("model state", modelState)
		log.Fatal(`actual state (-) not equal to model state (+): ` + pretty.Compare(actualState, modelState))
	}
}

// Starts docker container and sequentially runs steps
func (tr *TestRun) ExecuteSteps(wg *sync.WaitGroup, steps []Step) {
	defer wg.Done()
	fmt.Printf("=============== started %s tests ===============\n", tr.name)

	start := time.Now()
	for i, step := range steps {
		// print something the show the test is alive
		if i%10 == 0 {
			fmt.Printf("running %s: step %d\n", tr.name, i+1)
		}
		tr.runStep(step, *verbose)
	}

	fmt.Printf("=============== finished %s tests in %v ===============\n", tr.name, time.Since(start))
}

func (tr *TestRun) startDocker(binConfig binaryConfig) {
	fmt.Printf("=============== building %s testRun ===============\n", tr.name)
	scriptStr := "tests/integration/testnet-scripts/start-docker.sh " +
		tr.containerConfig.containerName + " " +
		tr.containerConfig.instanceName + " " +
		tr.localSdkPath + " " +
		binConfig.providerDirName + " " +
		binConfig.consumerDirName
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
		if verbose != nil && *verbose {
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

func getBinConfigFromFlags() binaryConfig {
	return binaryConfig{
		provBinName:          *provBinName,
		consBinName:          *consBinName,
		democracyConsBinName: *democracyConsBinName,
		providerDirName:      path.Base(*providerDirLoc),
		consumerDirName:      path.Base(*consumerDirLoc),
	}
}

// Copies custom source code for consumer and provider as specified
func copySourceCode(dirLocation string, newDirName string) {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err := exec.Command("docker", "exec",
		"cp", "-n", "-r",
		dirLocation,
		"./"+newDirName,
	).CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}
}
