package main

import (
	"fmt"
	"os"

	svrcmd "github.com/cosmos/cosmos-sdk/server/cmd"

	appparams "github.com/cosmos/interchain-security/v5/app/params"
	app "github.com/cosmos/interchain-security/v5/app/sovereign"

	"github.com/cosmos/interchain-security/v5/cmd/interchain-security-sd/cmd"
)

func main() {
	appparams.SetAddressPrefixes(app.AccountAddressPrefix)
	rootCmd := cmd.NewRootCmd()

	if err := svrcmd.Execute(rootCmd, "", app.DefaultNodeHome); err != nil {
		fmt.Fprintln(rootCmd.OutOrStderr(), err)
		os.Exit(1)
	}
}
