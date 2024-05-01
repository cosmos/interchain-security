package main

import (
	"os"

	"github.com/cosmos/cosmos-sdk/server"
	svrcmd "github.com/cosmos/cosmos-sdk/server/cmd"

	appparams "github.com/cosmos/interchain-security/v5/app/params"
	app "github.com/cosmos/interchain-security/v5/app/sovereign"
	"github.com/cosmos/interchain-security/v5/cmd/interchain-security-sd/cmd"
)

func main() {
	appparams.SetAddressPrefixes("consumer")
	rootCmd := cmd.NewRootCmd()
	if err := svrcmd.Execute(rootCmd, "", app.DefaultNodeHome); err != nil {
		switch e := err.(type) {
		case server.ErrorCode:
			os.Exit(e.Code)

		default:
			os.Exit(1)
		}
	}
}
