interchain-security-pd q provider pending-slash-packets --node tcp://7.7.7.253:26658
interchain-security-pd q provider pending-consumer-packets consu --node tcp://7.7.7.253:26658

	fmt.Println("#####", gjson.Get(string(bz), "packets"))
	packets := gjson.Get(string(bz), "packets").Array()
	fmt.Println("### PACKETS ####", packets)
	return len(packets)

	// // stepsThrottledDowntime creates two consumer initiated downtime slash events and relays packets
// func stepsThrottledDowntime(consumerName string) []Step {
// 	return []Step{
// 		{
// 			action: downtimeSlashAction{
// 				chain:      chainID(consumerName),
// 				validators: []validatorID{validatorID("bob"), validatorID("carol")},
// 			},
// 			state: State{
// 				// powers not affected on either chain yet
// 				chainID("provi"): ChainState{
// 					ValPowers: &map[validatorID]uint{
// 						validatorID("alice"): 511,
// 						validatorID("bob"):   500,
// 						validatorID("carol"): 500,
// 					},
// 				},
// 				chainID(consumerName): ChainState{
// 					ValPowers: &map[validatorID]uint{
// 						validatorID("alice"): 511,
// 						validatorID("bob"):   500,
// 						validatorID("carol"): 500,
// 					},
// 				},
// 			},
// 		},
// 		{
// 			action: relayPacketsAction{
// 				chain:   chainID("provi"),
// 				port:    "provider",
// 				channel: 0,
// 			},
// 			state: State{
// 				chainID("provi"): ChainState{
// 					ValPowers: &map[validatorID]uint{
// 						validatorID("alice"): 511,
// 						validatorID("bob"):   0,
// 						validatorID("carol"): 500, // not slashed due to throttling
// 					},
// 					GlobalSlashQueueSize: intPointer(1), // carol's slash request is throttled
// 				},
// 				chainID(consumerName): ChainState{
// 					// no updates received on consumer
// 					ValPowers: &map[validatorID]uint{
// 						validatorID("alice"): 511,
// 						validatorID("bob"):   500,
// 						validatorID("carol"): 500,
// 					},
// 					ConsumerChainQueueSize: intPointer(1),
// 				},
// 			},
// 		},
// 		// A block is incremented each action, hence why VSC is committed on provider,
// 		// and can now be relayed as packet to consumer
// 		{
// 			action: relayPacketsAction{
// 				chain:   chainID("provi"),
// 				port:    "provider",
// 				channel: 0,
// 			},
// 			state: State{
// 				chainID(consumerName): ChainState{
// 					ValPowers: &map[validatorID]uint{
// 						validatorID("alice"): 511,
// 						// first update (before throttling kicked in) now seen on consumer
// 						validatorID("bob"):   0,
// 						validatorID("carol"): 500,
// 					},
// 					ConsumerChainQueueSize: intPointer(0), // throttle queue was emptied
// 				},
// 			},
// 		},
// 		{
// 			action: relayPacketsAction{
// 				chain:   chainID("provi"),
// 				port:    "provider",
// 				channel: 0,
// 			},
// 			state: State{
// 				chainID("provi"): ChainState{
// 					ValPowers: &map[validatorID]uint{
// 						validatorID("alice"): 511,
// 						validatorID("bob"):   0,
// 						validatorID("carol"): 0, // slash meter was replenished and slash request was processed on provider
// 					},
// 					GlobalSlashQueueSize: intPointer(0),
// 				},
// 				chainID(consumerName): ChainState{
// 					ValPowers: &map[validatorID]uint{
// 						validatorID("alice"): 511,
// 						validatorID("bob"):   0,
// 						validatorID("carol"): 0, // consumer now sees a slash request that was throttled
// 					},
// 					ConsumerChainQueueSize: intPointer(0),
// 				},
// 			},
// 		},
// 	}
// }