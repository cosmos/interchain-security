package main

import (
	"fmt"
	"os"

	svrcmd "github.com/cosmos/cosmos-sdk/server/cmd"

	app "github.com/cosmos/interchain-security/v3/app/consumer-democracy"
	"github.com/cosmos/interchain-security/v3/cmd/interchain-security-cdd/cmd"
)

func main() {
	rootCmd := cmd.NewRootCmd()

	if err := svrcmd.Execute(rootCmd, "", app.DefaultNodeHome); err != nil {
		fmt.Fprintln(rootCmd.OutOrStderr(), err)
		os.Exit(1)
	}
}
