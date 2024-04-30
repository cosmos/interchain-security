package e2e

import (
	"bufio"
	"fmt"
	"log"
	"os/exec"
)

var verbose *bool //TODO: remove hack

func ExecuteCommandWithVerbosity(cmd *exec.Cmd, cmdName string, verbose bool) {
	if verbose {
		fmt.Println(cmdName+" cmd:", cmd.String())
	}

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
			fmt.Println(cmdName + ": " + out)
		}
	}
	if err := scanner.Err(); err != nil {
		log.Fatal(err)
	}
}

// Executes a command with verbosity specified by CLI flag
func ExecuteCommand(cmd *exec.Cmd, cmdName string) {
	ExecuteCommandWithVerbosity(cmd, cmdName, *verbose)
}
