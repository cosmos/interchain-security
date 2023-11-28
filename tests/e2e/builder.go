package main

import (
	"bytes"
	"fmt"
	"log"
	"os"
	"os/exec"
	"path"
)

func setupWorkspace(revision string, tmpDir string) error {
	log.Printf("Setting up worktree in '%s'", tmpDir)
	cmd := exec.Command("git", "worktree", "add",
		"--checkout", tmpDir, revision)
	var errbuf bytes.Buffer
	cmd.Stderr = &errbuf
	log.Printf("Running: %s", cmd.String())
	if err := cmd.Start(); err != nil {
		return err
	}
	if err := cmd.Wait(); err != nil {
		log.Printf("Error creating worktree (%v): %s", err, errbuf.String())
		return err
	}
	return nil
}

func cleanupWorkspace(workSpacePath string) error {
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
func buildDockerImage(imageName string, revision string, tmpDir string) error {
	log.Printf("Building ICS image for version %s", revision)

	if !dockerIsUp() {
		return fmt.Errorf("docker engine is not running")
	}
	workSpace := path.Join(tmpDir, revision)
	if err := setupWorkspace(revision, workSpace); err != nil {
		return err
	}
	defer cleanupWorkspace(workSpace)

	_, err := os.Stat(workSpace)
	if err != nil {
		log.Fatalf("Worktree creation for image build failed: %v", err)
	}

	log.Printf("Building docker image")
	// TODO: TBD if we should use option "--no-cache" here
	/* 	cmd := exec.Command("docker", "build", "--no-cache", "-t",
	fmt.Sprintf("cosmos-ics:%s", revision), "-f", "./Dockerfile", "./")
	*/

	cmd := exec.Command("docker", "build", "-t",
		fmt.Sprintf("cosmos-ics:%s", revision), "-f", "./Dockerfile", "./")

	cmd.Dir = workSpace

	if err := cmd.Start(); err != nil {
		log.Printf("Failed building docker image '%s': %v", revision, err)
		return err
	}
	if err := cmd.Wait(); err != nil {
		out, _ := cmd.CombinedOutput()
		log.Printf("Error building image (%v): %s", err, out)
		return err
	}
	return nil
}
