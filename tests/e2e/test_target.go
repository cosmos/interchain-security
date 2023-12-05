package main

import (
	"bufio"
	"fmt"
	"log"
	"os/exec"
	"strings"
)

type ExecutionTarget interface {
	GetTargetType() string
	GetLogs(path string) []byte
	GetStartChainScript(isProvider bool) string
	ExecCommand(name string, arg ...string) *exec.Cmd
	Start() error
	Stop() error
	Build() error
	Delete() error
}

type DockerContainer struct {
	targetConfig TargetConfig
	containerCfg ContainerConfig
	images       []string //images needed to build the target container
	ImageName    string
}

func (dc *DockerContainer) GetTargetType() string {
	return "docker"
}

func (dc *DockerContainer) GetLogs(path string) []byte {
	logs := []byte{}
	return logs
}

func generateImageName(version string, cfg TargetConfig) (string, error) {
	// identify a tag name
	tagName := ""
	if version == "" {
		tagName = "local" // this refers to build from local workspace
	} else {
		// use git hash of rev as docker image tag
		//cmd := exec.Command("git", "rev-parse", "--verify", "--short", version)
		cmd := exec.Command("git", "log", "--pretty=format:%h", "-n", "1", version)
		out, err := cmd.CombinedOutput()
		if err != nil {
			return "", fmt.Errorf("error getting hash for revision: %v, '%s'", err, out)
		}
		tagName = strings.TrimSpace(string(out))
	}

	imageName := "cosmos-ics"
	if cfg.useGaia {
		imageName += "_gaia"
		tagName += "-" + cfg.gaiaTag
	}
	if cfg.localSdkPath != "" {
		imageName += "_sdk"
	}

	return fmt.Sprintf("%s:%s", imageName, tagName), nil
}

// Build the docker image for the target container
func (dc *DockerContainer) Build() error {
	consumerVersion := dc.targetConfig.consumerVersion
	providerVersion := dc.targetConfig.providerVersion

	consumerImageName, err := generateImageName(consumerVersion, dc.targetConfig)
	if err != nil {
		return fmt.Errorf("failed building docker image: %v", err)
	}
	err = buildDockerImage(consumerImageName, consumerVersion, dc.targetConfig)
	if err != nil {
		return err
	}
	dc.images = append(dc.images, consumerImageName)

	if consumerVersion == "" && consumerVersion == providerVersion {
		dc.ImageName = consumerImageName
		return nil
	}

	// build image for provider as it's a different version to be run
	providerImageName, err := generateImageName(providerVersion, dc.targetConfig)
	if err != nil {
		return fmt.Errorf("failed building docker image: %v", err)
	}
	err = buildDockerImage(providerImageName, providerVersion, dc.targetConfig)
	if err != nil {
		return err
	}

	// build combined image using provider/consumer versions from images built above
	combinedImageName := fmt.Sprintf("cosmos-ics-combined:%s_%s",
		strings.Split(providerImageName, ":")[1],
		strings.Split(consumerImageName, ":")[1])
	cmd := exec.Command("docker", "build", "-f", "Dockerfile-Combined",
		"--build-arg", fmt.Sprintf("PROVIDER_IMAGE=%s", providerImageName),
		"--build-arg", fmt.Sprintf("CONSUMER_IMAGE=%s", consumerImageName),
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
		cmd := exec.Command("docker", "image", "rm", img)
		out, err := cmd.CombinedOutput()
		//TODO: ignore errors related to non-existing images
		if err != nil {
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
	return exec.Command("docker", args...)
}

// Get star-chain script to be used on target for a specific chain type
// Needed for different consumer/provider versions staged in one container
func (dc *DockerContainer) GetStartChainScript(isConsumer bool) string {
	startChainScript := "/testnet-scripts/start-chain.sh"
	if dc.targetConfig.providerVersion != "" && !isConsumer {
		log.Printf("Using start-chain script for provider version '%s'", dc.targetConfig.providerVersion)
		startChainScript = "/provider/testnet-scripts/start-chain.sh"
	}

	if dc.targetConfig.consumerVersion != "" && isConsumer {
		log.Printf("Using start-chain script for consumer version '%s'", dc.targetConfig.consumerVersion)
		startChainScript = "/consumer/testnet-scripts/start-chain.sh"
	}
	return startChainScript

}

// Startup the container
func (dc *DockerContainer) Start() error {
	fmt.Println("@@@@ starting existing containers", dc.containerCfg.InstanceName)
	// Remove existing containers from previous runs
	dc.Stop()

	// Run new test container instance with extended privileges.
	// Extended privileges are granted to the container here to allow for network namespace manipulation (bringing a node up/down)
	// See: https://docs.docker.com/engine/reference/run/#runtime-privilege-and-linux-capabilities
	cmd := exec.Command("docker", "run", "--name", dc.containerCfg.InstanceName,
		"--cap-add=NET_ADMIN", "--privileged", dc.ImageName,
		"/bin/bash", "/testnet-scripts/beacon.sh")

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
	fmt.Println("@@@@ stopping existing containers", dc.containerCfg.InstanceName)
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "stop", dc.containerCfg.InstanceName)
	bz, err := cmd.CombinedOutput()
	if err != nil {
		return fmt.Errorf("error stopping docker container: %v, %s", err, string(bz))
	}

	cmd = exec.Command("docker", "rm", dc.containerCfg.InstanceName)
	bz, err = cmd.CombinedOutput()
	if err != nil {
		return fmt.Errorf("error removing docker container: %v, %s", err, string(bz))
	}
	return err
}
