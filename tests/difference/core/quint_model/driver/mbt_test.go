package main

import (
	"log"
	"testing"

	"github.com/informalsystems/itf-go/itf"
)

func TestItfTrace(t *testing.T) {
	path := "trace.json"
	log.Printf("🟡 Testing trace %s", path)

	// Load trace
	trace := &itf.Trace{}
	if err := trace.LoadFromFile(path); err != nil {
		log.Fatalf("Error loading trace file: %s", err)
	}

	log.Println("Reading auxiliary information...")
	if trace.Vars[0] != "currentState" || trace.Vars[1] != "trace" {
		log.Fatalf("Error loading trace file %s: %s", path, "Variables should be currentState, trace")
	}

	log.Println("Reading the trace...")

	for index, state := range trace.States {
		log.Printf("Reading state %v", index)

		// modelState := state.VarValues["currentState"]
		trace := state.VarValues["trace"].Value.(itf.ListExprType)
		// fmt.Println(modelState)
		lastAction := trace[len(trace)-1].Value.(itf.MapExprType)

		actionKind := lastAction["kind"].Value.(string)
		switch actionKind {
		case "init":
			// start the chain(s)
		case "VotingPowerChange":
			node := lastAction["validator"].Value.(string)
			newVotingPower := lastAction["newVotingPower"].Value.(int64)
			log.Println(node, newVotingPower)
		case "EndAndBeginBlockForProvider":
			timeAdvancement := lastAction["timeAdvancement"].Value.(int64)
			consumersToStart := lastAction["consumersToStart"].Value.(itf.ListExprType)
			consumersToStop := lastAction["consumersToStop"].Value.(itf.ListExprType)
			log.Println(timeAdvancement, consumersToStart, consumersToStop)
		case "EndAndBeginBlockForConsumer":
			consumerChain := lastAction["consumerChain"].Value.(string)
			timeAdvancement := lastAction["timeAdvancement"].Value.(int64)

			log.Println(consumerChain, timeAdvancement)
		case "DeliverVscPacket":
			consumerChain := lastAction["consumerChain"].Value.(string)

			log.Println(consumerChain)
		case "DeliverVscMaturedPacket":
			consumerChain := lastAction["consumerChain"].Value.(string)

			log.Println(consumerChain)
		default:

			log.Fatalf("Error loading trace file %s, step %v: do not know action type %s",
				path, index, actionKind)
		}
	}
	t.FailNow()
}
