module ccv_logic {
    import extraSpells.* from "./extraSpells"

    // Things that are not modelled:
    // * Reward distribution
    // * Starting/Stopping chains during execution
    // * Slashes

    // Things that explicitly are modelled:
    // * Validator set changes are propagated from provider to consumers
    // * VSC packets mature

    // We assume that packet receive + ack happen synchronously, 
    // i.e. when the packet is delivered, the ack is delivered right afterwards.
    // This is because it is nontrivial in practice to get a relayer to relay a packet, but not its ack.
    
    // ===================
    // TYPE DEFINITIONS
    // ===================
    type Node = str
    type Chain = str
    type Power = int
    type VSCId = int
    type ValidatorSet = Node -> Power
    type Height = int
    type Timestamp = int
    // a list of validator sets per blocks, ordered by recency
    type VotingPowerHistory = List[ValidatorSet]

    type VSCPacket =
        {   
            // the identifier for this packet
            id: VSCId,
            // the new validator set. in the implementation, this would be a list of validator updates
            validatorSet: ValidatorSet,
            // the time at which the packet was sent. used to check whether packets have timed out.
            sendingTime: Timestamp
        }

    type VSCMaturedPacket = 
        {
            // the id of the VSCPacket that matured
            id: VSCId,
            // the time at which the packet was sent. used to check whether packets have timed out.
            sendingTime: Timestamp
        }


    // state that each chain needs to store, whether consumer or provider.
    type ChainState = {
        // Stores the list of voting powers that corresponded to voting powers 
        // at blocks over the chains entire existence.
        // Voting powers should be ordered by recency in descending order.
        votingPowerHistory: VotingPowerHistory,

        // the current validator set on each chain.
        // this will be included in the next block, but might not be final yet,
        // e.g. there may be more modifications in the current block.
        currentValidatorSet: ValidatorSet,

        // the latest timestamp that was comitted on chain
        lastTimestamp: Timestamp,
    }

    // Defines the current state of the provider chain. Essentially, all information here is stored by the provider on-chain (or could be derived purely by information that is on-chain).
    type ProviderState =
        {
            // the state that each chain needs to store
            chainState: ChainState,

            // Stores, for each consumer chain, the list of packets that have been sent to the consumer chain
            // and have not been received yet.
            // In the implementation, this would roughly be the unacknowledged packets on an ibc channel.
            outstandingPacketsToConsumer: Chain -> List[VSCPacket],

            // the set of received VSCMaturedPackets
            receivedMaturations: Set[VSCMaturedPacket],

            // stores which VSC Packets have been sent to compare with receivedMaturations to detect timeouts due to non-responsiveness
            sentVSCPackets: Chain -> Set[VSCPacket],

            // a mapping from (chainId, vscId) tuples to the timestamps of sent VSCPackets.
            vscSendTimestamps: (Chain, VSCId) -> Timestamp,

            // stores whether, in this block, the validator set has changed.
            // this is needed because the validator set might be considered to have changed, even though
            // it is still technically identical at our level of abstraction, e.g. a validator power change on the provider
            // might leave the validator set the same because a delegation and undelegation cancel each other out.
            providerValidatorSetChangedInThisBlock: bool,

            // stores, for each consumer chain, its current status -
            // unused, running, or stopped
            consumerStatus: Chain -> str,

            // a monotonic strictly increasing and positive ID that is used
            // to uniquely identify the VSCs sent to the consumer chains.
            runningVscId: int,
        }

    // Defines the current state of a consumer chain. This information is accessible to that consumer on-chain.
    type ConsumerState = {
        // the state that each chain needs to store
        chainState: ChainState,

        // Stores the maturation times for VSCPackets received by this consumer
        maturationTimes: VSCPacket -> Timestamp,

        // Stores the list of packets that have been sent to the provider chain by this consumer
        // and have not been received yet.
        // ordered by recency, so the head is the oldest packet.
        // In the implementation, essentially unacknowledged IBC packets.
        outstandingPacketsToProvider: List[VSCMaturedPacket],
    }

    // the state of the protocol consists of the composition of the state of one provider chain with potentially many consumer chains.
    type ProtocolState = {
        providerState: ProviderState,
        // the state of each consumer chain.
        // note that we assume that this contains all consumer chains that may ever exist,
        // and consumer chains that are currently not running will have providerState.consumerStatus == UNUSED or STOPPED.
        consumerStates: Chain -> ConsumerState
    }

    type Error = {
        message: str
    }

    // we return either a result or an error.
    // if hasError is true, newState may be arbitrary, but the error will be meaningful.
    // if hasError is false, error may be arbitrary, but newState will be meaningful.
    type Result = {
        hasError: bool,
        newState: ProtocolState,
        error: Error
    }

    pure def Ok(newState: ProtocolState): Result = {
        {
            hasError: false,
            newState: newState,
            error: {
                message: ""
            }
        }
    }

    pure def Err(msg: str): Result = {
        {
            hasError: true,
            newState: {
                providerState: {
                    chainState: {
                        votingPowerHistory: List(),
                        currentValidatorSet: Map(),
                        lastTimestamp: 0,
                    },
                    outstandingPacketsToConsumer: Map(),
                    receivedMaturations: Set(),
                    sentVSCPackets: Map(),
                    providerValidatorSetChangedInThisBlock: false,
                    consumerStatus: Map(),
                    runningVscId: 0,
                    vscSendTimestamps: Map(),
                },
                consumerStates: Map(),
            },
            error: {
                message: msg
            }
        }
    }

    // possible consumer statuses
    pure val STOPPED = "stopped" // the chain was once a consumer chain, but has been dropped by the provider.
    pure val RUNNING = "running" // the chain is currently a consumer chain. Running chains are those that get sent VSCPackets.
    pure val UNUSED = "unused" // the chain has never been a consumer chain, and is available to become one.
    // When a chain is dropped, it cannot become a consumer again - we assume that would be done by another consumer becoming running.

    // the provider chain.
    // given as a pure val so that we can switch cases based on
    // whether a chain is the provider or not
    pure val PROVIDER_CHAIN = "provider"

    // ===================
    // PROTOCOL PARAMETERS
    // ===================

    // For each chain, this defines the time between the initiation of an unbonding and its maturation.
    const UnbondingPeriodPerChain: Chain -> int

    // The maximum time duration between sending any VSCPacket to any consumer chain and receiving the
    // corresponding VSCMaturedPacket, without timing out the consumer chain and consequently removing it.
    const VscTimeout: int

    // The timeoutTimestamp for sending CCV packets.
    const CcvTimeoutTimestamp: int

    // ===================
    // PROTOCOL LOGIC contains the meat of the protocol
    // functions here roughly correspond to API calls that can be triggered from external sources
    // ===================
    
    // the power of a validator on the provider chain is changed to the given amount. We do not care how this happens,
    // e.g. via undelegations, or delegations, ...
    pure def votingPowerChange(currentState: ProtocolState, validator: Node, amount: int): Result = {
            if (amount < 0) {
                Err("Voting power changes must be positive")
            } else {
                pure val currentValidatorSet = currentState.providerState.chainState.currentValidatorSet
                pure val newValidatorSet = getUpdatedValidatorSet(currentValidatorSet, validator, amount)
                pure val newState = setProviderValidatorSet(currentState, newValidatorSet)
                Ok(newState)
            }
    }

    // Delivers the next queued VSCMaturedPacket from a consumer chain to the provider chain.
    // Only argument is the consumer chain, from which the packet will be delivered.
    pure def deliverPacketToProvider(currentState: ProtocolState, sender: Chain): Result = {
        if (not(isCurrentlyConsumer(sender, currentState.providerState))) {
            Err("Sender is not currently a consumer - must have 'running' status!")
        } else if (length(currentState.consumerStates.get(sender).outstandingPacketsToProvider) == 0) {
            Err("No outstanding packets to deliver")
        } else {
            val packet = currentState.consumerStates.get(sender).outstandingPacketsToProvider.head()
            val result = recvPacketOnProvider(currentState, sender, packet)
            val tmpState = result.newState
            if (result.hasError) {
                Err(result.error.message)
            } else {
                val result2 = removeOutstandingPacketFromConsumer(tmpState, sender)
                val tmpState2 = result2.newState
                val err2 = result2.error
                if (result2.hasError) {
                    Err(err2.message)
                } else {
                    Ok(tmpState2)
                }
            }
        }
    }

    // Ends a block on the provider. This means that the current validator set is committed on chain,
    // packets are queued, and the next block is started.
    pure def endAndBeginBlockForProvider(
        currentState: ProtocolState,
        // by how much the timestamp should be advanced,
        // i.e. the timestamp for the next block is oldTimestamp + timeAdvancement
        timeAdvancement: Timestamp,
        // a set of consumers that were unused before, but should be set to running now.
        consumersToStart: Set[Chain],
        // a set of consumers that were running before, but should be set to stopped now.
        consumersToStop: Set[Chain]): Result = {
        // commit the current running validator set on chain
        val currentProviderState = currentState.providerState
        val newChainState = currentProviderState.chainState.endAndBeginBlockShared(timeAdvancement)
        // modify the states of the consumers that should be started/stopped
        val res = currentProviderState.consumerStatus.getNewConsumerStatusMap(consumersToStart, consumersToStop)
        val newConsumerStatus = res._1
        val err = res._2
        if (err != "") {
            Err(err)
        } else {
            val newProviderState = currentProviderState.with(
                "chainState", newChainState
            ).with(
                "consumerStatus", newConsumerStatus
            )
            val providerStateAfterSending =
            if (currentProviderState.providerValidatorSetChangedInThisBlock and getRunningConsumers(currentState.providerState).size() > 0) {
                    newProviderState.sendVscPackets()
                } else {
                    newProviderState
                }
            Err("not implemented")
        }
    }

    pure def endAndBeginBlockForConsumer(
        currentState: ProtocolState,
        chain: Chain,
        // by how much the timestamp of the chain should be advanced for the next block
        timeAdvancement: Timestamp): Result = {
            if (currentState.consumerStates.keys().contains(chain)) {
                Err("chain is not a consumer")
            } else {
                // if the chain is not a consumer, return an error
                val currentConsumerState = currentState.consumerStates.get(chain)
                val newChainState = currentConsumerState.chainState.endAndBeginBlockShared(timeAdvancement)
                val newConsumerState = currentConsumerState.with(
                    "chainState", newChainState
                )
                val maturedPackets = newConsumerState.maturationTimes.keys().filter(
                    packet => 
                    val maturationTime = newConsumerState.maturationTimes.get(packet)
                    maturationTime <= newChainState.lastTimestamp
                )
                val newMaturationTimes = newConsumerState.maturationTimes.mapRemoveAll(maturedPackets)
                val newOutstandingPackets = newConsumerState.outstandingPacketsToProvider.concat(
                    maturedPackets.map(
                        packet => {
                            id: packet.id, 
                            sendingTime: newConsumerState.chainState.lastTimestamp
                        }
                    ).toList()
                )
                val newConsumerState2 = newConsumerState.with(
                    "maturationTimes", newMaturationTimes
                ).with(
                    "outstandingPacketsToProvider", newOutstandingPackets
                )
                val newConsumerStates = currentState.consumerStates.set(chain, newConsumerState2)
                val newState = currentState.with(
                    "consumerStates", newConsumerStates
                )
                Ok(newState)
            }
    }

    // ===================
    // UTILITY FUNCTIONS
    // which do not hold the core logic of the protocol, but are still part of it
    // ===================

    pure def getRunningConsumersFromMap(consumerStatus: Chain -> str): Set[Chain] = {
        consumerStatus.keys().filter(
            chain => consumerStatus.get(chain) == RUNNING
        )
    }

    pure def getStoppedConsumersFromMap(consumerStatus: Chain -> str): Set[Chain] = {
        consumerStatus.keys().filter(
            chain => consumerStatus.get(chain) == STOPPED
        )
    }

    // Returns the new ConsumerStatusMap according to the consumers to start/stop.
    // The second return is an error string: If it is not equal to "",
    // it contains an error message, and the first return should be ignored.
    pure def getNewConsumerStatusMap(
        currentConsumerStatusMap: Chain -> str,
        consumersToStart: Set[Chain],
        consumersToStop: Set[Chain]): (Chain -> str, str) = {
            val runningConsumers = getRunningConsumersFromMap(currentConsumerStatusMap)
            val stoppedConsumers = getStoppedConsumersFromMap(currentConsumerStatusMap)
            // if a consumer is both started and stopped, this is an error
            if (consumersToStart.intersect(consumersToStop).size() > 0) {
                (currentConsumerStatusMap, "Cannot start and stop a consumer at the same time")
            } else {
                // if a consumer is started, it must be unused
                if (consumersToStart.intersect(runningConsumers).size() > 0) {
                    (currentConsumerStatusMap, "Cannot start a consumer that is already running")
                } else {
                    // if a consumer is stopped, it must be running
                    if (consumersToStop.intersect(stoppedConsumers).size() > 0) {
                        (currentConsumerStatusMap, "Cannot stop a consumer that is not running")
                    } else {
                        // if a consumer is started, it must be unused
                        val newConsumerStatusMap = currentConsumerStatusMap.keys().mapBy(
                            (chain) => 
                            if (consumersToStart.contains(chain)) {
                                RUNNING
                            } else if (consumersToStop.contains(chain)) {
                                STOPPED
                            } else {
                                currentConsumerStatusMap.get(chain)
                            }
                        )
                        (newConsumerStatusMap, "")
                    }
                }
            }
        }

    // Takes the currentValidatorSet and puts it as the newest set of the voting history
    pure def enterCurValSetIntoBlock(chainState: ChainState): ChainState = {
        chainState.with(
            "votingPowerHistory", chainState.votingPowerHistory.prepend(
                chainState.currentValidatorSet
            )
        )
    }

    // Advances the timestamp in the chainState by timeAdvancement
    pure def advanceTime(chainState: ChainState, timeAdvancement: Timestamp): ChainState = {
        chainState.with(
            "lastTimestamp", chainState.lastTimestamp + timeAdvancement
        )
    }

    // common logic to update the chain state, used by both provider and consumers.
    pure def endAndBeginBlockShared(chainState: ChainState, timeAdvancement: Timestamp): ChainState = {
        chainState.enterCurValSetIntoBlock().advanceTime(timeAdvancement)
    }

    // returns the providerState with the following modifications:
    // * sends VSCPackets to all running consumers
    // * increments the runningVscId
    // This should only be called when the provider chain is ending a block,
    // and only when the running validator set is considered to have changed
    // and there is a consumer to send a packet to.
    pure def sendVscPackets(providerState: ProviderState): ProviderState = {
        providerState.with(
            // send VSCPackets to consumers
            "outstandingPacketsToConsumer", 
            // if running validator set is considered to have changed and there is a consumer to send a packet to
            if (providerState.providerValidatorSetChangedInThisBlock
                and getRunningConsumers(providerState).size() > 0) {
                    // then send a packet to each running consumer
                    providerState.consumerStatus.keys().mapBy(
                        // go through all potential consumers
                        (consumer) => 
                        val packetQueue = providerState.outstandingPacketsToConsumer.get(consumer)
                        // if the consumer is running, send a packet
                        if (isCurrentlyConsumer(consumer, providerState)) {
                            packetQueue.append(
                                {
                                    id: providerState.runningVscId,
                                    validatorSet: providerState.chainState.currentValidatorSet,
                                    sendingTime: providerState.chainState.lastTimestamp
                                }
                            )
                        } else {
                            // otherwise, leave the queue as-is
                            packetQueue
                        }
                    )
                } else {
                    // running validator set is not considered to have changed
                    // ...so don't send any packets
                    providerState.outstandingPacketsToConsumer
                }
            ).with(
                // the validator set has not changed yet in the new block
                "providerValidatorSetChangedInThisBlock", false
            ).with(
                "runningVscId", providerState.runningVscId + 1
            ) 
    }

    // receives a given packet (sent by the provider) on the consumer. The arguments are the consumer chain that is receiving the packet, and the packet itself.
    // To receive a packet, modify the running validator set (not the one entered into the block yet,
    // but the candidate that would be put into the block if it ended now)
    // and store the maturation time for the packet.
    pure def recvPacketOnConsumer(currentState: ProtocolState, receiver: Chain, packet: VSCPacket): Result = {
        if(not(isCurrentlyConsumer(receiver, currentState.providerState))) {
            Err("Receiver is not currently a consumer - must have 'running' status!")
        } else {
            // update the running validator set, but not the history yet,
            // as that only happens when the next block is started
            val currentConsumerState = currentState.consumerStates.get(receiver)
            val newConsumerState = currentConsumerState.with(
                "chainState",
                currentConsumerState.chainState.with(
                    "currentValidatorSet", packet.validatorSet
                )
            ).with(
                "maturationTimes",
                currentConsumerState.maturationTimes.put(
                    packet, 
                    currentConsumerState.chainState.lastTimestamp + UnbondingPeriodPerChain.get(receiver)
                )
            )
            val newConsumerStates = currentState.consumerStates.set(receiver, newConsumerState)
            val newState = currentState.with(
                "consumerStates", newConsumerStates
            )
            Ok(newState)
        }
    }

    // receives a given packet on the provider. The arguments are the consumer chain that sent the packet, and the packet itself.
    // To receive a packet, add it to the list of received maturations.
    pure def recvPacketOnProvider(currentState: ProtocolState, sender: Chain, packet: VSCMaturedPacket): Result = {
        if (not(isCurrentlyConsumer(sender, currentState.providerState))) {
            Err("Sender is not currently a consumer - must have 'running' status!")
        } else {
            val currentReceivedMaturations = currentState.providerState.receivedMaturations
            val newReceivedMaturations = currentReceivedMaturations.add(packet)
            val newProviderState = currentState.providerState.with(
                "receivedMaturations", newReceivedMaturations
            )
            val newState = currentState.with(
                "providerState", newProviderState
            )
            Ok(newState)
        }
    }

    // removes the oldest outstanding packet from the consumer. on-chain, this would happen when the packet is acknowledged.
    // only the oldest packet can be removed, since we model ordered channels.
    pure def removeOutstandingPacketFromConsumer(currentState: ProtocolState, sender: Chain): Result = {
        val currentOutstandingPackets = currentState.consumerStates.get(sender).outstandingPacketsToProvider
        val newOutstandingPackets = currentOutstandingPackets.tail()
        val newConsumerState = currentState.consumerStates.get(sender).with(
            "outstandingPacketsToProvider", newOutstandingPackets
        )
        val newConsumerStates = currentState.consumerStates.set(sender, newConsumerState)
        val newState = currentState.with(
            "consumerStates", newConsumerStates
        )
        Ok(newState)
    }

    // Updates the given oldValidatorSet by setting the validator to newVotingPower.
    // If newVotingPower is zero, the validator is removed.
    pure def getUpdatedValidatorSet(oldValidatorSet: ValidatorSet, validator: Node, newVotingPower: int): ValidatorSet =
        if (newVotingPower > 0) 
        oldValidatorSet.put(validator, newVotingPower)
        else
        oldValidatorSet.mapRemove(validator)

    // Returns a ProtocolState where the current validator set on the provider is set to 
    // newValidatorSet.
    pure def setProviderValidatorSet(currentState: ProtocolState, newValidatorSet: ValidatorSet): ProtocolState = {
        pure val newChainState = currentState.providerState.chainState.with(
            "currentValidatorSet", newValidatorSet
        )
        currentState.with(
            "providerState", 
                currentState.providerState.with(
                    "chainState", newChainState
            )
        )
    }

    // Returns true if the given chain is currently a running consumer, false otherwise.
    pure def isCurrentlyConsumer(chain: Chain, providerState: ProviderState): bool = {
        val status = providerState.consumerStatus.get(chain)
        status == RUNNING
    }

    // Returns the set of all consumer chains that currently have the status RUNNING.
    pure def getRunningConsumers(providerState: ProviderState): Set[Chain] = {
        providerState.consumerStatus.keys().filter(
            chain => providerState.consumerStatus.get(chain) == RUNNING
        )
    }
}

module ccv_tests {
    import ccv_logic.*

    // // UTILITY FUNCTIONS & ACTIONS
    // def wasValidatorSetOnProvider(validatorSet: ValidatorSet): bool = {
    //     votingPowerHistories.get(ProviderChain).toSet().exists(
    //         historicalValSet => historicalValSet == validatorSet
    //     )
    // }

    // def getCurrentValidatorSet(chain: Chain): ValidatorSet = 
    //     votingPowerHistories.get(chain).head()

    // // returns true if the consumer has timed out and should be dropped
    // def consumerTimedOut(consumer: Chain): bool =
    //     any {
    //         // either a package from provider to consumer has timed out
    //         outstandingPacketsToConsumer.get(consumer).select(
    //             packet => packet.timeout <= curChainTimes.get(consumer)
    //         ).length() > 0,
    //         // or a package from consumer to provider has timed out
    //         outstandingPacketsToProvider.get(consumer).select(
    //             packet => packet.timeout <= curChainTimes.get(ProviderChain)
    //         ).length() > 0,
    //         // or the inactivity timeout has passed since a VSCPacket was sent to the consumer, but the
    //         // provider has not received a VSCMaturedPacket for it
    //         val packetsWithoutResponse = sentVSCPackets.get(consumer).filter( // get packets without response
    //             packet => 
    //             not(receivedMaturations.exists(
    //                 maturedPacket => maturedPacket.id == packet.id
    //             ))
    //         )
    //         // among those, get packets where inactivity timeout has passed
    //         packetsWithoutResponse.filter(
    //             packet => 
    //             val sentAt = curChainTimes.get(ProviderChain) - PacketTimeout // compute when the packet was sent
    //             val timesOutAt = sentAt + InactivityTimeout // compute when the packet times out
    //             timesOutAt <= curChainTimes.get(ProviderChain)
    //         ).size() > 0
    //     }

    // // utility action that leaves all provider state untouched
    // action PROVIDER_NOOP(): bool = 
    //     all {
    //         receivedMaturations' = receivedMaturations,
    //     }

    // // utility action that leaves all consumer state untouched
    // action CONSUMER_NOOP(): bool = 
    //     all {
    //         maturationTimes' = maturationTimes,
    //     }
    

    // // MODEL ACTIONS

    // // the power of a validator on the provider chain is changed to the given amount. We do not care how this happens,
    // // e.g. via undelegations, or delegations, ...
    // action doVotingPowerChange(validator: Node, amount: int): bool =
    //     // for the provider chain, we need to adjust the voting power history
    //     // by adding a new set
    //     all {
    //         amount >= 0,
    //         val newValidatorSet = getCurrentValidatorSet(ProviderChain).getUpdatedValidatorSet(validator, amount)
    //         // set the running validator set on the provider chain, but don't update the history yet
    //         runningValidatorSet' = runningValidatorSet.set(ProviderChain, newValidatorSet),
    //         // no packets are sent yet, these are only sent on endAndBeginBlock
    //         RegisterNewOutstandingPackets(outstandingPacketsToConsumer),
    //         outstandingPacketsToProvider' = outstandingPacketsToProvider,
    //         receivedMaturations' = receivedMaturations,
    //         CONSUMER_NOOP,
    //         // voting power history is only updated on endAndBeginBlock
    //         votingPowerHistories' = votingPowerHistories,
    //         // consumer statusses do not change
    //         consumerStatus' = consumerStatus,
    //         // chain times do not change
    //         curChainTimes' = curChainTimes,
    //         // the validator set is considered to have changed
    //         providerValidatorSetChangedInThisBlock' = true,
    //     }

    // // deliver the next outstanding packet from the consumer to the provider.
    // // since this model assumes a single provider chain, this just takes a single chain as argument.
    // action recvPacketOnProvider(consumer: Chain): bool = all {
    //     // ensure there is a packet to be received
    //     outstandingPacketsToProvider.get(consumer).length() > 0,
    //     // remove packet from outstanding packets
    //     val newPacketQueue = outstandingPacketsToProvider.get(consumer).tail()
    //     outstandingPacketsToProvider' = outstandingPacketsToProvider.set(consumer, newPacketQueue),
    //     // register the packet as received
    //     val maturedPacket = outstandingPacketsToProvider.get(consumer).head()
    //     receivedMaturations' = receivedMaturations.add(maturedPacket),
    //     CONSUMER_NOOP,
    //     RegisterNewOutstandingPackets(outstandingPacketsToConsumer),
    //     votingPowerHistories' = votingPowerHistories,
    //     // no validator set changes are made
    //     runningValidatorSet' = runningValidatorSet,
    //     // consumer statusses do not change
    //     consumerStatus' = consumerStatus,
    //     // chain times do not change
    //     curChainTimes' = curChainTimes,
    //     // the validator set was not changed by this action (but might have been changed before in this block)
    //     providerValidatorSetChangedInThisBlock' = providerValidatorSetChangedInThisBlock
    // }

    // // deliver the next outstanding packet from the provider to the consumer.
    // // since this model assumes a single provider chain, this just takes a single chain as argument.
    // action recvPacketOnConsumer(consumer: Chain): bool = all {
    //     // ensure there is a packet to be received
    //     outstandingPacketsToConsumer.get(consumer).length() > 0,
    //     // remove packet from outstanding packets
    //     val newPacketQueue = outstandingPacketsToConsumer.get(consumer).tail()
    //     val newOutstandingPackets = outstandingPacketsToConsumer.set(consumer, newPacketQueue)
    //     RegisterNewOutstandingPackets(newOutstandingPackets),
    //     val packet = outstandingPacketsToConsumer.get(consumer).head()
    //     all {
    //         // update the running validator set, but not the history yet,
    //         // as that only happens when the next block is started
    //         runningValidatorSet' = runningValidatorSet.set(consumer, packet.validatorSet),
    //         // add the new packet and store its maturation time
    //         val newMaturationTimes = maturationTimes.get(consumer).put(packet, curChainTimes.get(consumer) + UnbondingPeriod.get(consumer))
    //         maturationTimes' = maturationTimes.set(consumer, newMaturationTimes)
    //     },
    //     PROVIDER_NOOP,
    //     votingPowerHistories' = votingPowerHistories,
    //     outstandingPacketsToProvider' = outstandingPacketsToProvider,
    //     // consumer statusses do not change
    //     consumerStatus' = consumerStatus,
    //     // chain times do not change
    //     curChainTimes' = curChainTimes,
    //     // the validator set was not changed by this action (but might have been changed before in this block)
    //     providerValidatorSetChangedInThisBlock' = providerValidatorSetChangedInThisBlock
    // }

    // // ends the current block and starts the next block for a given chain.
    // action endAndBeginBlock(chain: Chain): bool = any {
    //     all {
    //       chain == ProviderChain,
    //       endAndBeginBlockForProvider,
    //     },
    //     all {
    //         chain != ProviderChain,
    //         endAndBeginBlockForConsumer(chain),
    //     }
    // }

    // // gets the updated history for the current chain when ending a block, i.e. the
    // // running validator set is added to the history if different from the last one.
    // def getUpdatedHistory(chain: Chain): List[ValidatorSet] =
    //     // update voting power history if the validator set changed
    //     val newValidatorSet = runningValidatorSet.get(ProviderChain)
    //     val oldValidatorSet = votingPowerHistories.get(ProviderChain).head()
    //     if (newValidatorSet != oldValidatorSet) 
    //         votingPowerHistories.get(ProviderChain).prepend(newValidatorSet)
    //     else
    //         votingPowerHistories.get(ProviderChain)


    // action endAndBeginBlockForProvider(): bool = all {
    //     // update the voting power history
    //     votingPowerHistories' = votingPowerHistories.set(ProviderChain, getUpdatedHistory(ProviderChain)),
    //     // the running validator set is now for sure the current validator set,
    //     // so start with it in the next block
    //     runningValidatorSet' = runningValidatorSet,
    //     // send VSCPackets to consumers
    //     val newOutstandingPackets = 
    //         // if running validator set is considered to have changed
    //         if (providerValidatorSetChangedInThisBlock)
    //             // then send a packet to each running consumer
    //             outstandingPacketsToConsumer.keys().mapBy(
    //                 (consumer) => 
    //                 val packetQueue = outstandingPacketsToConsumer.get(consumer)
    //                 if (consumerStatus.get(consumer) == RUNNING) {
    //                     packetQueue.append(
    //                         {
    //                             id: packetQueue.length(),
    //                             validatorSet: runningValidatorSet.get(ProviderChain),
    //                             timeout: curChainTimes.get(ProviderChain) + PacketTimeout
    //                         }
    //                     )
    //                 } else {
    //                     packetQueue
    //                 }
    //             )
    //         else
    //             // otherwise, don't send any packets
    //             outstandingPacketsToConsumer
    //     RegisterNewOutstandingPackets(newOutstandingPackets),
    //     CONSUMER_NOOP,
    //     // no packets are sent to the provider
    //     outstandingPacketsToProvider' = outstandingPacketsToProvider,
    //     // do not receive any maturations
    //     receivedMaturations' = receivedMaturations,
    //     // consumer statusses do not change
    //     consumerStatus' = consumerStatus,
    //     // chain times do not change
    //     curChainTimes' = curChainTimes,
    //     // the validator set was definitely not changed in the new block yet, so set to false
    //     providerValidatorSetChangedInThisBlock' = false
    // }

    // action endAndBeginBlockForConsumer(consumer: Chain): bool = all {
    //     ConsumerChains.contains(consumer),
    //     // update the voting power history
    //     votingPowerHistories' = votingPowerHistories.set(consumer, getUpdatedHistory(consumer)),
    //     // the running validator set is now for sure the current validator set,
    //     // so start with it in the next block
    //     runningValidatorSet' = runningValidatorSet,
    //     // compute mature packets whose maturation time has passed
    //     val maturedPackets = maturationTimes.get(consumer).keys().filter(
    //         packet => 
    //         val maturationTime = maturationTimes.get(consumer).get(packet)
    //         maturationTime <= curChainTimes.get(consumer)
    //     )
    //     all {
    //         // remove matured packets from the maturation times
    //         maturationTimes' = maturationTimes.set(consumer, maturationTimes.get(consumer).mapRemoveAll(maturedPackets)),
    //         // send matured packets
    //         outstandingPacketsToProvider' = outstandingPacketsToProvider.set(
    //             consumer, 
    //             // construct VSCMaturedPackets from the matured VSCPackets
    //             outstandingPacketsToProvider.get(consumer).concat(
    //                 maturedPackets.map(packet => {id: packet.id, timeout: 5}).toList()
    //             )
    //         )
    //     },
    //     PROVIDER_NOOP,
    //     // no packets are sent to consumer or received by it
    //     RegisterNewOutstandingPackets(outstandingPacketsToConsumer),
    //     // consumer statusses do not change
    //     consumerStatus' = consumerStatus,
    //     // chain times do not change
    //     curChainTimes' = curChainTimes,
    //     // the validator set was not changed by this action (but might have been changed before in this block)
    //     // also, this is only a new block for a consumer, so the change variable shouldn't be reset
    //     providerValidatorSetChangedInThisBlock' = providerValidatorSetChangedInThisBlock
    // }

    // // advance timestamps for maps nondeterministically
    // action AdvanceTime(): bool = 
    //         val advanceAmounts = curChainTimes.keys().mapBy(
    //             chain =>    
    //             nondet amount = oneOf(1.to(10))
    //             amount
    //         )
    //         AdvanceTimeByMap(advanceAmounts)

    // // the timestamp for each chain is advanced by the given amount
    // action AdvanceTimeByMap(advancementAmount: Chain -> int): bool = all
    //     {
    //         curChainTimes' = curChainTimes.keys().mapBy(
    //             chain => 
    //             curChainTimes.get(chain) + advancementAmount.get(chain)
    //         ),
    //         // all other variables are left untouched
    //         votingPowerHistories' = votingPowerHistories,
    //         runningValidatorSet' = runningValidatorSet,
    //         outstandingPacketsToProvider' = outstandingPacketsToProvider,
    //         RegisterNewOutstandingPackets(outstandingPacketsToConsumer),
    //         receivedMaturations' = receivedMaturations,
    //         maturationTimes' = maturationTimes,
    //         // chain times do not change
    //         consumerStatus' = consumerStatus,
    //         // the validator set was not changed by this action (but might have been changed before in this block)
    //         providerValidatorSetChangedInThisBlock' = providerValidatorSetChangedInThisBlock
    //     }

    // // each consumer chain may advance in the order
    // // some events may necessitate a transition, e.g. timeouts.
    // // shouldAdvance gives, for each consumer chain, whether it should advance if possible.
    // // if a chain has to advance, e.g. due to timeouts, or may not advance, the value will have no effect.
    // action AdvanceConsumers(shouldAdvance: Chain -> bool): bool = 
    //     val newConsumerStatus = consumerStatus.keys().mapBy(
    //         chain => 
    //         val curStatus = consumerStatus.get(chain)
    //         if (curStatus == UNUSED) {
    //             if (shouldAdvance.get(chain))
    //             {
    //                 RUNNING
    //             } else {
    //                 UNUSED
    //             }
    //         }
    //         else if (curStatus == RUNNING) {
    //             // the chain may transition to stopped.
    //             // it is *forced* to stop if a packet timed out,
    //             // or if the inactivity timeout has passed
    //             if(consumerTimedOut(chain)) {
    //                 STOPPED
    //             } else {
    //                 if (shouldAdvance.get(chain)) {
    //                     RUNNING
    //                 } else {
    //                     STOPPED
    //                 }
    //             }
    //         } else {
    //             // stopped chains cannot restart, we assume a new chain would be started in that case
    //             STOPPED
    //         }
    //         )
    //     all {
    //         consumerStatus' = newConsumerStatus,
    //         // all other variables are left untouched
    //         votingPowerHistories' = votingPowerHistories,
    //         runningValidatorSet' = runningValidatorSet.keys().mapBy(
    //             chain => 
    //             if (newConsumerStatus.get(chain) == RUNNING and consumerStatus.get(chain) == UNUSED) 
    //             // consumers that went from unused to running start with the current validator set on the provider
    //             { 
    //                 runningValidatorSet.get(ProviderChain) 
    //             } else {
    //                 runningValidatorSet.get(chain)
    //             }
    //         ),
    //         outstandingPacketsToProvider' = outstandingPacketsToProvider,
    //         RegisterNewOutstandingPackets(outstandingPacketsToConsumer),
    //         receivedMaturations' = receivedMaturations,
    //         maturationTimes' = maturationTimes,
    //         // chain times do not change
    //         curChainTimes' = curChainTimes,
    //         // the validator set was not changed by this action (but might have been changed before in this block)
    //         providerValidatorSetChangedInThisBlock' = providerValidatorSetChangedInThisBlock
    //     }

    // // Updates the outstandingPacketsToConsumer and sentVSCPackets variables
    // action RegisterNewOutstandingPackets(newOutstandingPackets: Chain -> List[VSCPacket]): bool = 
    //     all {
    //         outstandingPacketsToConsumer' = newOutstandingPackets,
    //         StoreSentPackets(newOutstandingPackets),
    //     }


    // // stores the VSCPackets sent in this step in sentVSCPackets
    // action StoreSentPackets(newOutstandingPackets: Chain -> List[VSCPacket]): bool = 
    //     sentVSCPackets' = sentVSCPackets.keys().mapBy(
    //         (chain) => 
    //         sentVSCPackets.get(chain).union(newOutstandingPackets.get(chain).toSet())
    //     )

    
    // // the main step action 
    // action step: bool = any {
    //     AdvanceTime,
    //     nondet node = oneOf(Nodes)
    //     nondet amount = oneOf(1.to(10))
    //     votingPowerChange(node, amount),
    //     recvPacketOnProvider(oneOf(ConsumerChains)),
    //     recvPacketOnConsumer(oneOf(ConsumerChains)),
    //     nondet chain = oneOf(chains)
    //     endAndBeginBlock(chain),
    //     val shouldAdvance = ConsumerChains.mapBy(
    //         chain => 
    //         nondet should = oneOf(Set(true, false))
    //         should
    //     )
    //     AdvanceConsumers(shouldAdvance),
    // }

    // pure val nodePowerSet = Nodes.powerset()

    // def getArbitraryValidatorSet(): ValidatorSet = 
    //     nondet numValidators = oneOf(1.to(Nodes.size()))
    //     // toList has nondeterministic behaviour, so this gets arbitrary validators
    //     nondet validators = oneOf(nodePowerSet.filter(s => s.size() == numValidators))
    //     validators.mapBy(
    //         validator => 
    //         nondet votingPower = oneOf(1.to(10))
    //         votingPower
    //     )

    // // INITIALIZATION
    // action init: bool = 
    // all {
    //     val validatorSets = chains.mapBy(
    //         (chain) => 
    //     // provider chain gets an arbitrary validator set, consumer chains have none
    //         if (chain == ProviderChain) getArbitraryValidatorSet else Map()
    //     )
    //     all {
    //         votingPowerHistories' = chains.mapBy(
    //             (chain) => 
    //             List(validatorSets.get(chain))
    //         ),
    //         runningValidatorSet' = validatorSets,
    //     },
    //     // each chain starts at time 0
    //     curChainTimes' = chains.mapBy(
    //         (chain) => 0
    //     ),
    //     // all consumer chains are unused
    //     consumerStatus' = chains.mapBy(chain => UNUSED),
    //     // no packets are outstanding
    //     outstandingPacketsToProvider' = chains.mapBy(chain => List()),
    //     outstandingPacketsToConsumer' = chains.mapBy(chain => List()),
    //     // no maturations have been received by provider
    //     receivedMaturations' = Set(),
    //     // no packets have been sent to consumers
    //     sentVSCPackets' = chains.mapBy(chain => Set()),
    //     // no packets have been received by consumers, so no maturation times set
    //     maturationTimes' = chains.mapBy(chain => Map()),
    //     // validator set was not changed yet
    //     providerValidatorSetChangedInThisBlock' = false
    // }

    // // PROPERTIES

    // // Every validator set on any consumer chain MUST either be or
    // // have been a validator set on the provider chain.
    // val ValidatorSetReplication: bool = 
    //     chains.forall(
    //         chain => chain.getCurrentValidatorSet().wasValidatorSetOnProvider()
    //     )

    // // TESTS
    // run VSCHappyPathTest: bool = {
    //     init
    //     // trigger a votingPowerChange on the provider chain
    //     .then(votingPowerChange("A", 10))
    //     // endAndBeginBlock on provider. No consumer chains are running, so no packets are sent
    //     .then(endAndBeginBlock(ProviderChain))
    //     .then(all {
    //         // no packet was sent
    //         assert(outstandingPacketsToConsumer.get("chain1").length() == 0),
    //         // advance chain1 to running
    //         AdvanceConsumers(NoStatusAdvancement.set("chain1", true))
    //     })
    //     // consumer chain should have current validator set from provider
    //     .then(
    //         all { 
    //             // since consumer chain just started, its assumed to have the validator set from provider
    //             assert(runningValidatorSet.get("chain1") == runningValidatorSet.get(ProviderChain)),
    //             // trigger a votingPowerChange on the provider chain
    //             votingPowerChange("B", 10)
    //         }
    //     )
    //     .then(
    //         val valSet = runningValidatorSet.get(ProviderChain)
    //         endAndBeginBlock(ProviderChain)
    //         // now the provider should send a packet on block end
    //         .then(all {
    //             // a packet was sent
    //             assert(outstandingPacketsToConsumer.get("chain1").length() == 1),
    //             // deliver the packet to the consumer
    //             recvPacketOnConsumer("chain1")
    //         })
    //         .then(
    //             // consumer needs to end a block before it has the new validator set
    //             endAndBeginBlock("chain1")
    //         )
    //         .then(all {
    //             // the consumer should have the new validator set
    //             assert(runningValidatorSet.get("chain1") == valSet),
    //             // put a last action to satisfy the action effect
    //             AdvanceConsumers(NoStatusAdvancement)
    //         })
    //     )
    // }

    // // utility: the set of consumers currently running
    // val RunningConsumers: Set[Chain] = 
    //     ConsumerChains.filter(chain => consumerStatus.get(chain) == RUNNING)

    // // MODEL STATE
    // // --SHARED STATE

    // // Stores, for each chain, the list of voting powers that corresponded to voting powers 
    // // at blocks over its entire existence.
    // // Voting powers should be ordered by recency in descending order.
    // var votingPowerHistories: Chain -> List[ValidatorSet]

    // // the current validator set on each chain.
    // // this will be included in the next block, but might not be final yet,
    // // e.g. there may be more modifications in the current block.
    // var runningValidatorSet: Chain -> ValidatorSet

    // // the current timestamp for each chain
    // var curChainTimes: Chain -> Timestamp

    // // stores, for each chain, its current status -
    // // unused, running, or stopped
    // var consumerStatus: Chain -> str

    // // --CHANNELS
    // // Stores, for each consumer chain, the list of packets that have been sent to the provider chain
    // // and have not been received yet.
    // var outstandingPacketsToProvider: Chain -> List[VSCMaturedPacket]

    // // Stores, for each consumer chain, the list of packets that have been sent to the consumer chain
    // // and have not been received yet.
    // var outstandingPacketsToConsumer: Chain -> List[VSCPacket]


    // // --CONSUMER STATE
    // // Stores the maturation times for VSCPackets received by consumers
    // var maturationTimes: Chain -> (VSCPacket -> Timestamp)

    // // --PROVIDER STATE
    // // the set of VSCMaturedPackets received by the provider chain
    // var receivedMaturations: Set[VSCMaturedPacket]

    // // stores which VSC Packets have been sent to compare with receivedMaturations to detect timeouts due to non-responsiveness
    // var sentVSCPackets: Chain -> Set[VSCPacket]

    // // stores whether, in this step, the validator set considered to be changed.
    // // this is needed because the validator set might be considered to have changed, even though
    // // it is still technically identical at our level of abstraction, e.g. a validator power change on the provider
    // // might leave the validator set the same because a delegation and undelegation cancel each other out.
    // var providerValidatorSetChangedInThisBlock: bool

    // // utility: a struct summarizing the current state
    // val state = 
    //     {
    //         votingPowerHistories: votingPowerHistories,
    //         runningValidatorSet: runningValidatorSet,
    //         curChainTimes: curChainTimes,
    //         consumerStatus: consumerStatus,
    //         outstandingPacketsToProvider: outstandingPacketsToProvider,
    //         outstandingPacketsToConsumer: outstandingPacketsToConsumer,
    //         maturationTimes: maturationTimes,
    //         receivedMaturations: receivedMaturations,
    //         sentVSCPackets: sentVSCPackets,
    //     }

    // // set of identifiers of potential nodes
    // pure val Nodes: Set[Node] = 
    //     Set("A", "B", "C", "D", "E", "F", "G", "H", "I", "J")

    // // the set of consumer chains
    // pure val ConsumerChains: Set[Chain] = 
    //     Set("chain1", "chain2", "chain3")

    // // The singular provider chain.
    // pure val ProviderChain: Chain = 
    //     "provider"
        
    // pure val chains = ConsumerChains.union(Set(ProviderChain))

    // // length of the unbonding period on each chain
    // pure val UnbondingPeriod: Chain -> int = chains.mapBy(
    //     (chain) => 
    //     10
    // )

    // // the time until a packet times out
    // pure val PacketTimeout: int = 
    //     5

    // // the time until a consumer chain is dropped by the provider due to inactivity
    // pure val InactivityTimeout: int =
    //     10

    // // utility: a map assigning each chain to 0, used for not advancing timestamps
    // pure val NoTimeAdvancement: Chain -> int = chains.mapBy(
    //     (chain) => 
    //     0
    // )


    // // utility: a map assigning each chain to false, used for not advancing consumer status
    // pure val NoStatusAdvancement: Chain -> bool = chains.mapBy(
    //     (chain) => 
    //     false
    // )
}
