package main

import (
	"bufio"
	"fmt"
	"log"
	"os"
	"os/exec"
	"strings"

	"golang.org/x/mod/semver"
)

type ExecutionTarget interface {
	GetTargetConfig() TargetConfig
	GetTestScriptPath(isConsumer bool, script string) string
	// ExecCommand: when executed the command will run and return after completion
	ExecCommand(name string, arg ...string) *exec.Cmd
	// ExecDetachedCommand: when executed the command will be run in the background and call will return immediately
	ExecDetachedCommand(name string, args ...string) *exec.Cmd
	Start() error
	Stop() error
	Build() error
	Delete() error
	Info() string
}
type TargetConfig struct {
	gaiaTag         string
	localSdkPath    string
	useGaia         bool
	providerVersion string
	consumerVersion string
}
type DockerContainer struct {
	targetConfig TargetConfig
	containerCfg ContainerConfig
	images       []string // images needed to build the target container
	ImageName    string
}

func createTarget(testCfg TestConfig, targetCfg TargetConfig) (DockerContainer, error) {
	targetCfg.providerVersion = testCfg.providerVersion
	targetCfg.consumerVersion = testCfg.consumerVersion
	target := DockerContainer{
		targetConfig: targetCfg,
		containerCfg: testCfg.containerConfig,
	}

	err := target.Build()
	if err != nil {
		return target, fmt.Errorf("failed building target %s\n: %v", target.Info(), err)
	}
	return target, nil
}

func (dc *DockerContainer) GetTargetConfig() TargetConfig {
	return dc.targetConfig
}

// Build the docker image for the target container
func (dc *DockerContainer) Build() error {
	consumerVersion := dc.targetConfig.consumerVersion
	providerVersion := dc.targetConfig.providerVersion

	consumerImageName, err := getDockerImage(consumerVersion, dc.targetConfig, false)
	if err != nil {
		return fmt.Errorf("failed building docker image: %v", err)
	}
	dc.images = append(dc.images, consumerImageName)

	// if consumer and provider version are identical we're done and
	// no combined image from different versions needs to be created
	if consumerVersion == providerVersion {
		dc.ImageName = consumerImageName
		return nil
	}

	// build image for provider as it's a different version to be run
	providerImageName, err := getDockerImage(providerVersion, dc.targetConfig, false)
	if err != nil {
		return err
	}
	dc.images = append(dc.images, providerImageName)

	// build combined image using provider/consumer versions from images built above
	combinedImageName := fmt.Sprintf("cosmos-ics-combined:%s_%s",
		strings.Split(providerImageName, ":")[1],
		strings.Split(consumerImageName, ":")[1])

	// For some version combinations the latest 'genesis transformer' does not support the required transformation
	// transformation function of the client of the consumer version needs to be used and not the latest
	transformerImage := "ghcr.io/cosmos/interchain-security:latest"
	if semver.IsValid(consumerVersion) && semver.IsValid(providerVersion) &&
		semver.Compare(consumerVersion, "v3.3.0") <= 0 && semver.Compare(providerVersion, "v3.3.0") < 0 {
		transformerImage = "ghcr.io/cosmos/interchain-security:v3.3.0"
	}

	fmt.Println("Transformer used:", transformerImage)
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "build", "-f", "Dockerfile.combined",
		"--build-arg", fmt.Sprintf("PROVIDER_IMAGE=%s", providerImageName),
		"--build-arg", fmt.Sprintf("CONSUMER_IMAGE=%s", consumerImageName),
		"--build-arg", fmt.Sprintf("TRANSFORMER_IMAGE=%s", transformerImage),
		"-t", combinedImageName,
		".")
	out, err := cmd.CombinedOutput()
	if err != nil {
		log.Printf("Failed running: %v", cmd)
		return fmt.Errorf("error building combined docker image: %v, %s", err, string(out))
	}
	dc.images = append(dc.images, combinedImageName)
	dc.ImageName = combinedImageName
	return err
}

func (dc *DockerContainer) Delete() error {
	for _, img := range dc.images {
		// Keep images from registry (but latest)
		if !strings.HasPrefix(img, ICS_DOCKER_REGISTRY) && strings.HasSuffix(img, "latest") {
			continue
		}

		//#nosec G204 -- Bypass linter warning for spawning subprocess with variable
		cmd := exec.Command("docker", "image", "rm", img)
		out, err := cmd.CombinedOutput()
		if err != nil && !strings.Contains(string(out), "No such image") {
			log.Printf("failed deleting image '%v' (%v): %v", cmd, err, string(out))
		}
	}
	return nil
}

// ExecCommand returns the command struct to execute the named program with
// given arguments on the current target (docker container)
func (dc *DockerContainer) ExecCommand(name string, arg ...string) *exec.Cmd {
	args := []string{"exec", dc.containerCfg.InstanceName, name}
	args = append(args, arg...)
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	return exec.Command("docker", args...)
}

// ExecDetachedCommand returns the command struct to execute the named program with
// given arguments on the current target (docker container) in _detached_ mode
func (dc *DockerContainer) ExecDetachedCommand(name string, arg ...string) *exec.Cmd {
	args := []string{"exec", "-d", dc.containerCfg.InstanceName, name}
	args = append(args, arg...)
	//#nosec G204 -- Bypass linter warning for spawning subprocess with variable
	return exec.Command("docker", args...)
}

// Get path to testnet-script on target for a specific chain type
// Needed for different consumer/provider versions staged in one container
func (dc *DockerContainer) GetTestScriptPath(isConsumer bool, script string) string {
	path := "/testnet-scripts"
	// in case the provider and consumer version differ the test-scripts are in dedicated directories on the target
	// for each of them (see Docker.combined)
	if dc.targetConfig.providerVersion != dc.targetConfig.consumerVersion {
		if isConsumer {
			fmt.Printf("Using script path for consumer version '%s'\n", dc.targetConfig.consumerVersion)
			path = "/consumer/testnet-scripts"
		} else {
			fmt.Printf("Using script path for provider version '%s'\n", dc.targetConfig.providerVersion)
			path = "/provider/testnet-scripts"
		}
	}
	// no combined image (see Dockerfile)
	return strings.Join([]string{path, script}, string(os.PathSeparator))
}

// Startup the container
func (dc *DockerContainer) Start() error {
	// Remove existing containers from previous runs
	if err := dc.Stop(); err != nil {
		return err
	}
	fmt.Println("Starting container: ", dc.containerCfg.InstanceName)

	// Run new test container instance with extended privileges.
	// Extended privileges are granted to the container here to allow for network namespace manipulation (bringing a node up/down)
	// See: https://docs.docker.com/engine/reference/run/#runtime-privilege-and-linux-capabilities
	beaconScript := dc.GetTestScriptPath(false, "beacon.sh")
	//#nosec G204 -- subprocess launched with potential tainted input (no production code)
	cmd := exec.Command("docker", "run", "--name", dc.containerCfg.InstanceName,
		"--cap-add=NET_ADMIN", "--privileged", dc.ImageName,
		"/bin/bash", beaconScript)

	cmdReader, err := cmd.StdoutPipe()
	if err != nil {
		log.Fatal(err)
	}
	cmd.Stderr = cmd.Stdout

	if err := cmd.Start(); err != nil {
		log.Fatal(err)
	}
	scanner := bufio.NewScanner(cmdReader)

	// Wait until container is up
	for scanner.Scan() {
		out := scanner.Text()
		if verbose != nil && *verbose {
			fmt.Println("startDocker: " + out)
		}
		if out == "beacon!!!!!!!!!!" {
			return nil
		}
	}
	if err := scanner.Err(); err != nil {
		return fmt.Errorf("error bringing up container: %v", err)
	}

	err = cmd.Wait()
	return fmt.Errorf("starting container exited with error: %v", err)
}

// Stop will stop the container and remove it
func (dc *DockerContainer) Stop() error {
	fmt.Println("Stopping existing containers: ", dc.containerCfg.InstanceName)
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "stop", dc.containerCfg.InstanceName)
	bz, err := cmd.CombinedOutput()
	if err != nil && !strings.Contains(string(bz), "No such container") {
		return fmt.Errorf("error stopping docker container: %v, %s", err, string(bz))
	}

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd = exec.Command("docker", "rm", dc.containerCfg.InstanceName)
	bz, err = cmd.CombinedOutput()
	if err != nil && !strings.Contains(string(bz), "No such container") {
		return fmt.Errorf("error removing docker container: %v, %s", err, string(bz))
	}
	return nil
}

// Info returns target information
func (dc *DockerContainer) Info() string {
	providerVersion := dc.targetConfig.providerVersion
	consumerVersion := dc.targetConfig.consumerVersion
	if dc.targetConfig.consumerVersion == "" {
		consumerVersion = "default (current workspace)"
	}

	if dc.targetConfig.providerVersion == "" {
		providerVersion = "default (current workspace)"
	}

	return fmt.Sprintf(`
Docker
	Consumer version: %s
	Provider version: %s
	Docker image: %s
	Docker container: %s`,
		consumerVersion,
		providerVersion,
		dc.ImageName,
		dc.containerCfg.InstanceName)
}
