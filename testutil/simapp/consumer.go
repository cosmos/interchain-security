package simapp

import (
	appWasm "github.com/CosmWasm/wasmd/app"
	evidencekeeper "github.com/cosmos/cosmos-sdk/x/evidence/keeper"
	slashingkeeper "github.com/cosmos/cosmos-sdk/x/slashing/keeper"
	ibctesting "github.com/cosmos/ibc-go/v3/testing"
	appConsumer "github.com/cosmos/interchain-security/app/consumer"
	ibcconsumerkeeper "github.com/cosmos/interchain-security/x/ccv/consumer/keeper"
)

type ConsumerChainType uint8

const (
	Minimal ConsumerChainType = iota
	CosmWasm
)

func GetAllConsumerChainTypes() []ConsumerChainType {
	return []ConsumerChainType{
		Minimal,
		CosmWasm,
	}
}

// TODO: introduce interface that would be implemented by all consumer App structs and add this 3 methods
func GetConsumerKeeper(app ibctesting.TestingApp) ibcconsumerkeeper.Keeper {
	switch app.(type) {
	case *appConsumer.App:
		return app.(*appConsumer.App).ConsumerKeeper
	case *appWasm.WasmApp:
		return app.(*appWasm.WasmApp).ConsumerKeeper
	default:
		panic("Unknown consumer chain type!")
	}
}

func GetSlashingKeeper(app ibctesting.TestingApp) slashingkeeper.Keeper {
	switch app.(type) {
	case *appConsumer.App:
		return app.(*appConsumer.App).SlashingKeeper
	case *appWasm.WasmApp:
		return app.(*appWasm.WasmApp).GetSlashingKeeper()
	default:
		panic("Unknown consumer chain type!")
	}
}

func GetEvidenceKeeper(app ibctesting.TestingApp) evidencekeeper.Keeper {
	switch app.(type) {
	case *appConsumer.App:
		return app.(*appConsumer.App).EvidenceKeeper
	case *appWasm.WasmApp:
		return app.(*appWasm.WasmApp).GetEvidenceKeeper()
	default:
		panic("Unknown consumer chain type!")
	}
}
