package main

import (
	"bytes"
	"encoding/json"
	"fmt"
	"log"
	"os"
	"os/exec"
	"strings"
)

const ICS_DOCKER_REGISTRY = "ghcr.io/cosmos/interchain-security"

type DockerImgInfo struct {
	Id           string `json:"Id"`
	Architecture string `json:"Architecture"`
	Os           string `json:"Os"`
	Config       struct {
		Labels struct {
			Maintainer string `json:"maintainer"`
			Created    string `json:"org.opencontainers.image.created"`
			Revision   string `json:"org.opencontainers.image.revision"`
			Version    string `json:"org.opencontainers.image.version"`
		} `json:"Labels"`
	} `json:"Config"`
}

// setupWorkSpace checks out given revision in a tmp directory
// and returns the path where the workspace is located
func setupWorkSpace(revision string) (string, error) {
	workSpace := "./"
	if revision == "" {
		return workSpace, nil
	}
	workSpace, err := os.MkdirTemp(os.TempDir(), "e2eWorkTree_")
	if err != nil {
		return "", fmt.Errorf("error creating temp directory %v", err)
	}

	fmt.Printf("Setting up worktree in '%s'\n", workSpace)

	//#nosec G204 -- Bypass linter warning for spawning subprocess with variable
	cmd := exec.Command("git", "worktree", "add",
		"--force", "--checkout", workSpace, revision)
	out, err := cmd.CombinedOutput()
	fmt.Println("Running: ", cmd.String())
	if err != nil {
		log.Printf("Error creating worktree (%v): %s", err, string(out))
		return "", err
	}

	// Check if workspace exists
	_, err = os.Stat(workSpace)
	if err != nil {
		log.Fatalf("image build failed. invalid workspace: %v", err)
	}

	return workSpace, nil
}

// cleanupWorkSpace removes the created worktree
func cleanupWorkSpace(workSpacePath string) error {
	if workSpacePath == "./" {
		// no worktree was used for build
		return nil
	}
	cmd := exec.Command("git", "worktree", "remove", workSpacePath)
	cmd.Stderr = cmd.Stdout
	if err := cmd.Start(); err != nil {
		log.Printf("Failed removing git worktree '%s' used for docker image creation", workSpacePath)
		return err
	}
	return cmd.Wait()
}

// generateImageName
func generateImageName(version string, cfg TargetConfig) (string, error) {
	// identify a tag name
	tagName := ""
	if version == "" {
		tagName = "local" // this refers to build from local workspace
	} else {
		// use git hash of rev as docker image tag
		cmd := exec.Command("git", "log", "--pretty=format:%h", "-n", "1", version)
		out, err := cmd.CombinedOutput()
		if err != nil {
			return "", fmt.Errorf("error generating docker image name: no hash found for revision '%v': '%s'", err, string(out))
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

// Check if docker is running
func dockerIsUp() bool {
	cmd := exec.Command("docker", "info")
	var errbuf bytes.Buffer
	cmd.Stderr = &errbuf
	if err := cmd.Run(); err != nil {
		log.Printf("Docker engine is not running (%v): %s", err, errbuf.String())
		return false
	}
	return true
}

// getDockerImage provides a ICS docker image for a given version
func getDockerImage(version string, cfg TargetConfig, noCache bool) (string, error) {
	// try to pull the image first from the GitHub interchain registry
	imgName, err := pullDockerImage(version, cfg)
	if err == nil {
		fmt.Println("Using docker image from registry: ", imgName)
		return imgName, nil
	}

	imgName, err = buildDockerImage(version, cfg, noCache)
	return imgName, err
}

// getImageInfo returns information about a local docker image
func getImageInfo(image string) ([]DockerImgInfo, error) {
	// check if the image is already available locally
	cmd := exec.Command("docker", "inspect", "--type", "image", image)
	out, err := cmd.CombinedOutput()
	if err != nil {
		return nil, err
	}
	imgInfos := []DockerImgInfo{}
	if err = json.Unmarshal(out, &imgInfos); err != nil {
		return nil, fmt.Errorf("error unmarshalling image information: %v", err)
	}
	return imgInfos, nil
}

// pullDockerImage pulls ICS image for a given tag from GitHub docker registry of ICS.
// Checkout "https://github.com/cosmos/interchain-security/pkgs/container/interchain-security"
// for existing tagged versions
func pullDockerImage(tag string, targetConfig TargetConfig) (string, error) {
	// the image path for the GH registry
	imageURL := fmt.Sprintf("ghcr.io/cosmos/interchain-security:%s", tag)

	// get information about local pulled image for this version
	infos, err := getImageInfo(imageURL)
	if err == nil {
		for _, imgInfo := range infos {
			if imgInfo.Architecture == "amd64" && imgInfo.Os == "linux" {
				return imageURL, nil
			}
		}
	}

	// images in ghcr.io registry are not build with support for gaia or private SDK path
	if targetConfig.useGaia || targetConfig.localSdkPath != "" {
		return "", fmt.Errorf("no image supporting target configuration found")
	}

	fmt.Println("No matching local image found for", tag, "-> Checking registry")
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments
	cmd := exec.Command("docker", "pull", "--platform", "linux/amd64", imageURL)
	out, err := cmd.CombinedOutput()
	if err != nil {
		return "", fmt.Errorf("no matching image found in registry: %v, %s", err, string(out))
	}

	return imageURL, nil
}

// bootstrapSDK in workspace to use custom SDK setup if required
func bootstrapSDK(workSpace string, targetCfg TargetConfig) error {
	sdkPath := strings.Join([]string{workSpace, "cosmos-sdk"}, string(os.PathSeparator))
	err := os.RemoveAll(sdkPath) // delete old SDK directory
	if err != nil {
		return fmt.Errorf("error deleting SDK directory from workspace: %v", err)
	}
	if targetCfg.localSdkPath != "" {
		fmt.Printf("Using local SDK version from %s\n", targetCfg.localSdkPath)
		//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
		cmd := exec.Command("cp", "-n", "-r", targetCfg.localSdkPath, sdkPath)
		out, err := cmd.CombinedOutput()
		if err != nil {
			log.Printf("Error running command %v: %s", cmd, string(out))
			return fmt.Errorf("error setting up local SDK: %v, %s", err, string(out))
		}
	} else {
		fmt.Println("Using default SDK version")
	}
	return nil
}

// Build docker image of ICS for a given version
// version can be anything valid to create a git workspace from, e.g revision or tag
func buildDockerImage(version string, targetCfg TargetConfig, noCache bool) (string, error) {
	if !dockerIsUp() {
		return "", fmt.Errorf("docker engine is not running")
	}

	// get a docker image name based on version and target configuration
	imageName, err := generateImageName(version, targetCfg)
	if err != nil {
		return "", err
	}
	fmt.Println("Building ICS image", imageName)

	// if a revision is provided the related version will be staged
	// on a separate worktree (note: revision should _not_ be checked out already elsewhere).
	// which will be deleted after image creation
	workSpace, err := setupWorkSpace(version)
	if err != nil {
		return "", err
	}
	defer cleanupWorkSpace(workSpace)

	// Stage SDK if needed
	err = bootstrapSDK(workSpace, targetCfg)
	if err != nil {
		return "", err
	}

	// Build the docker image
	dockerFile := "Dockerfile"
	args := []string{"build", "-t", imageName}
	if noCache {
		args = append(args, "--no-cache")
	}

	if targetCfg.useGaia && targetCfg.gaiaTag != "" {
		dockerFile = "Dockerfile.gaia"
		args = append(args, "--build-arg", fmt.Sprintf("USE_GAIA_TAG=%s", targetCfg.gaiaTag))
	}
	args = append(args, "-f", dockerFile, "./")

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", args...)
	cmd.Dir = workSpace
	out, err := cmd.CombinedOutput()
	if err != nil && !noCache {
		// Retry image creation from pristine state by enforcing --no-cache
		log.Printf("Image creation failed '%v'. Re-trying without cache!", err)
		return buildDockerImage(version, targetCfg, true)
	}
	if err != nil {
		return "", fmt.Errorf("building docker image failed running '%v' (%v): %s", cmd, err, out)
	}

	return imageName, err
}
