package main

import (
	"bytes"
	"fmt"
	"log"
	"os"
	"os/exec"
	"strings"
)

// setupWorkSpace checks out given revision in a tmp directory
// and returns the path where the workspace is located
func setupWorkSpace(revision string) (string, error) {
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
	return workSpace, nil
}

// cleanupWorkSpace removes the created worktree
func cleanupWorkSpace(workSpacePath string) error {
	cmd := exec.Command("git", "worktree", "remove", workSpacePath)
	cmd.Stderr = cmd.Stdout
	if err := cmd.Start(); err != nil {
		log.Printf("Failed removing git worktree '%s' used for docker image creation", workSpacePath)
		return err
	}
	return cmd.Wait()
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

// Build docker image of ICS for a given revision
func buildDockerImage(imageName, revision string, targetCfg TargetConfig, noCache bool) error {
	fmt.Printf("Building ICS %s image %s\n", revision, imageName)
	if !dockerIsUp() {
		return fmt.Errorf("docker engine is not running")
	}

	workSpace := "./"
	var err error = nil
	// if a revision is provided the related version will be staged
	// on a separate worktree (note: revision should _not_ be checked out already elsewhere).
	// which will be deleted after image creation
	if revision != "" {
		workSpace, err = setupWorkSpace(revision)
		if err != nil {
			return err
		}
		defer cleanupWorkSpace(workSpace)
	}

	// Check if workspace exists
	_, err = os.Stat(workSpace)
	if err != nil {
		log.Fatalf("image build failed. invalid workspace: %v", err)
	}

	// Use custom SDK setup if required
	sdkPath := strings.Join([]string{workSpace, "cosmos-sdk"}, string(os.PathSeparator))
	err = os.RemoveAll(sdkPath) //delete old SDK directory
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
		return buildDockerImage(imageName, revision, targetCfg, true)
	}
	if err != nil {
		return fmt.Errorf("building docker image failed running '%v' (%v): %s", cmd, err, out)
	}

	return err
}
