module CCVTypes {
    import Time.* from "./Time"

    type Node = str
    type Chain = str
    type Power = int
    type VSCId = int
    type ValidatorSet = Node -> Power
    type Height = int
    // a list of validator sets per blocks, ordered by recency
    type VotingPowerHistory = List[ValidatorSet]

    type VSCPacket =
        {   
            // the identifier for this packet
            id: VSCId,
            // the new validator set. in the implementation, this would be a list of validator updates
            validatorSet: ValidatorSet,
            // the time at which the packet was sent. used to check whether packets have timed out.
            sendingTime: Time
        }

    type VSCMaturedPacket = 
        {
            // the id of the VSCPacket that matured
            id: VSCId,
            // the time at which the packet was sent. used to check whether packets have timed out.
            sendingTime: Time
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
        lastTimestamp: Time,
    }

    // utility function: returns a chain state that is initialized minimally.
    pure def GetEmptyChainState(): ChainState = 
        {
            votingPowerHistory: List(),
            currentValidatorSet: Map(),
            lastTimestamp: 0,
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
            sentVSCPackets: Chain -> List[VSCPacket],

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

    // utility function: returns a provider state that is initialized minimally.
    pure def GetEmptyProviderState(): ProviderState = 
        {
            chainState: GetEmptyChainState,
            outstandingPacketsToConsumer: Map(),
            receivedMaturations: Set(),
            sentVSCPackets: Map(),
            providerValidatorSetChangedInThisBlock: false,
            consumerStatus: Map(),
            runningVscId: 0,
        }
        

    // Defines the current state of a consumer chain. This information is accessible to that consumer on-chain.
    type ConsumerState = {
        // the state that each chain needs to store
        chainState: ChainState,

        // Stores the maturation times for VSCPackets received by this consumer
        maturationTimes: VSCPacket -> Time,

        // Stores the list of packets that have been sent to the provider chain by this consumer
        // and have not been received yet.
        // ordered by recency, so the head is the oldest packet.
        // In the implementation, essentially unacknowledged IBC packets.
        outstandingPacketsToProvider: List[VSCMaturedPacket],
    }

    // utility function: returns a consumer state that is initialized minimally.
    pure def GetEmptyConsumerState(): ConsumerState = 
        {
            chainState: GetEmptyChainState,
            maturationTimes: Map(),
            outstandingPacketsToProvider: List(),
        }

    // the state of the protocol consists of the composition of the state of one provider chain with potentially many consumer chains.
    type ProtocolState = {
        providerState: ProviderState,
        // the state of each consumer chain.
        // note that we assume that this contains all consumer chains that may ever exist,
        // and consumer chains that are currently not running will have providerState.consumerStatus == UNUSED or STOPPED.
        consumerStates: Chain -> ConsumerState
    }

    // gets a protocol state that is initialized minimally.
    pure def GetEmptyProtocolState(): ProtocolState = 
        {
            providerState: GetEmptyProviderState,
            consumerStates: Map(),
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
}

module CCV {
    // Implements the core logic of the cross-chain validation protocol.

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
    
    import extraSpells.* from "./extraSpells"
    import Time.* from "./Time"
    import CCVTypes.*
  

    // ===================
    // PROTOCOL PARAMETERS
    // ===================

    // the set of all possible consumer chains.
    const ConsumerChains: Set[Chain]

    // For each chain, this defines the time between the initiation of an unbonding and its maturation.
    const UnbondingPeriodPerChain: Chain -> int

    // The maximum time duration between sending any VSCPacket to any consumer chain and receiving the
    // corresponding VSCMaturedPacket, without timing out the consumer chain and consequently removing it.
    const VscTimeout: int

    // The timeoutTimestamp for sent packets. Can differ by chain.
    const CcvTimeout: Chain -> int

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
    // If this packet will time out on the provider on delivery,
    // the consumer will be dropped.
    // The first return is the result of the operation, the second result is a boolean
    // that indicates whether the consumer timed out or not.
    // If the result has an error, the second return should be ignored.
    pure def deliverPacketToProvider(currentState: ProtocolState, sender: Chain): (Result, bool) = {
        if (not(isCurrentlyConsumer(sender, currentState.providerState))) {
            (Err("Sender is not currently a consumer - must have 'running' status!"), false)
        } else if (length(currentState.consumerStates.get(sender).outstandingPacketsToProvider) == 0) {
            (Err("No outstanding packets to deliver"), false)
        } else {
            val packet = currentState.consumerStates.get(sender).outstandingPacketsToProvider.head()
            // if the packet has timed out, drop the consumer. its state doesn't matter anymore
            val timeout = CcvTimeout.get(sender)
            if(packet.sendingTime + CcvTimeout.get(sender) < currentState.providerState.chainState.lastTimestamp) {
                // drop consumer
                val result = getNewConsumerStatusMap(
                    currentState.providerState.consumerStatus,
                    Set(),
                    Set(sender)
                )

                val newConsumerStatus = result._1
                val err = result._2
                if (err != "") {
                    (Err(err), false)
                } else {
                    val newProviderState = currentState.providerState.with(
                        "consumerStatus", newConsumerStatus
                    )
                    val newState = currentState.with(
                        "providerState", newProviderState
                    )
                    (Ok(newState), true) // true because the packet timed out
                }
            } else {
                // the packet has not timed out, so receive it on the provider
                val result = recvPacketOnProvider(currentState, sender, packet)
                val tmpState = result.newState
                if (result.hasError) {
                    (Err(result.error.message), false)
                } else {
                    val result2 = removeOutstandingPacketFromConsumer(tmpState, sender)
                    val tmpState2 = result2.newState
                    val err2 = result2.error
                    if (result2.hasError) {
                        (Err(err2.message), false)
                    } else {
                        (Ok(tmpState2), false) // false because the packet did not time out
                    }
                }
            }
        }
    }   

    // Defines a test state to test the deliverPacketToProvider function against.
    pure val _DeliverPacketToProvider_TestState =
        val currentState = GetEmptyProtocolState
        val sender = "sender"
        val providerState = currentState.providerState
        val consumerState = GetEmptyConsumerState
        // add the consumer to the consumerStates
        val consumerStates = currentState.consumerStates.put(sender, consumerState)
        val providerState2 = providerState.with(
            "consumerStatus", providerState.consumerStatus.put(sender, RUNNING)
        )
        val providerState3 = providerState2.with(
            "outstandingPacketsToConsumer", providerState2.outstandingPacketsToConsumer.put(sender, List({
                id: 0,
                validatorSet: Map(),
                sendingTime: 0
            }))
        )
        currentState.with(
            "providerState", providerState3
        ).with(
            "consumerStates", consumerStates
        )

    // Delivers the next queued VSCPacket from the provider chain to a consumer chain.
    // Only argument is the consumer chain, to which the packet will be delivered.
    // If this packet will time out on the consumer on delivery,
    // the consumer will be dropped.
    // The first return is the result of the operation, the second result is a boolean
    // that indicates whether the consumer timed out or not.
    // If the result has an error, the second return should be ignored.
    pure def deliverPacketToConsumer(currentState: ProtocolState, receiver: Chain): (Result, bool) = {
        if (not(isCurrentlyConsumer(receiver, currentState.providerState))) {
            (Err("Receiver is not currently a consumer - must have 'running' status!"), false)
        } else if (length(currentState.providerState.outstandingPacketsToConsumer.get(receiver)) == 0) {
            (Err("No outstanding packets to deliver"), false)
        } else {
            val packet = currentState.providerState.outstandingPacketsToConsumer.get(receiver).head()
            // check if the consumer timed out
            if (packet.sendingTime + CcvTimeout.get(PROVIDER_CHAIN) < currentState.consumerStates.get(receiver).chainState.lastTimestamp) {
                // drop consumer
                val result = getNewConsumerStatusMap(
                    currentState.providerState.consumerStatus,
                    Set(),
                    Set(receiver)
                )

                val newConsumerStatus = result._1
                val err = result._2
                if (err != "") {
                    (Err(err), false)
                } else {
                    val newProviderState = currentState.providerState.with(
                        "consumerStatus", newConsumerStatus
                    )
                    val newState = currentState.with(
                        "providerState", newProviderState
                    )
                    (Ok(newState), true) // true because the packet timed out
                }
            } else {
                // the packet has not timed out, so receive it on the consumer
                val result = recvPacketOnConsumer(currentState, receiver, packet)
                val tmpState = result.newState
                if (result.hasError) {
                    (Err(result.error.message), false)
                } else {
                    val result2 = removeOutstandingPacketFromProvider(tmpState, receiver)
                    val tmpState2 = result2.newState
                    val err2 = result2.error
                    if (result2.hasError) {
                        (Err(err2.message), false)
                    } else {
                        (Ok(tmpState2), false) // false because the packet did not time out
                    }
                }
            }
        }
    }



    // Ends a block on the provider. This means that the current validator set is committed on chain,
    // packets are queued, and the next block is started. Also, consumers that have passed
    // the VSCTimeout without responding to a pending vscpacket are dropped.
    pure def endAndBeginBlockForProvider(
        currentState: ProtocolState,
        // by how much the timestamp should be advanced,
        // i.e. the timestamp for the next block is oldTimestamp + timeAdvancement
        timeAdvancement: Time,
        // a set of consumers that were unused before, but should be set to running now.
        consumersToStart: Set[Chain],
        // a set of consumers that were running before, but should be set to stopped now.
        // This argument only needs to contain "voluntary" stops -
        // forced stops, e.g. because a consumer timed out,
        // will be added automatically. 
        consumersToStop: Set[Chain]): Result = {
        // commit the current running validator set on chain
        val currentProviderState = currentState.providerState
        val newChainState = currentProviderState.chainState.endAndBeginBlockShared(timeAdvancement)
        val providerStateAfterTimeAdvancement = currentProviderState.with(
            "chainState", newChainState
        )

        // check for VSC timeouts
        val timedOutConsumers = getRunningConsumers(providerStateAfterTimeAdvancement).filter(
            consumer => 
            val res = TimeoutDueToVSCTimeout(currentState, consumer)
            res._1
        )

        // modify the states of the consumers that should be started/stopped
        val res = providerStateAfterTimeAdvancement.consumerStatus.getNewConsumerStatusMap(consumersToStart, consumersToStop.union(timedOutConsumers))
        val newConsumerStatus = res._1
        val err = res._2
        if (err != "") {
            Err(err)
        } else {
            val providerStateAfterConsumerAdvancement = providerStateAfterTimeAdvancement.with(
                "consumerStatus", newConsumerStatus
            )
            val providerStateAfterSending =
            if (currentProviderState.providerValidatorSetChangedInThisBlock and getRunningConsumers(currentState.providerState).size() > 0) {
                    providerStateAfterConsumerAdvancement.sendVscPackets()
                } else {
                    providerStateAfterConsumerAdvancement
                }
            val newState = currentState.with(
                "providerState", providerStateAfterSending
            )
            Ok(newState)
        }
    }

    pure def endAndBeginBlockForConsumer(
        currentState: ProtocolState,
        chain: Chain,
        // by how much the timestamp of the chain should be advanced for the next block
        timeAdvancement: Time): Result = {
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
    pure def advanceTime(chainState: ChainState, timeAdvancement: Time): ChainState = {
        chainState.with(
            "lastTimestamp", chainState.lastTimestamp + timeAdvancement
        )
    }

    // common logic to update the chain state, used by both provider and consumers.
    pure def endAndBeginBlockShared(chainState: ChainState, timeAdvancement: Time): ChainState = {
        chainState.enterCurValSetIntoBlock().advanceTime(timeAdvancement)
    }

    // returns the providerState with the following modifications:
    // * sends VSCPackets to all running consumers
    // * increments the runningVscId
    // This should only be called when the provider chain is ending a block,
    // and only when the running validator set is considered to have changed
    // and there is a consumer to send a packet to.
    pure def sendVscPackets(providerState: ProviderState): ProviderState = {
        val newSentPacketsPerConsumer = ConsumerChains.mapBy(
            (consumer) => 
            // if validator set changed and the consumer is running, send a packet
            if (providerState.providerValidatorSetChangedInThisBlock and 
                isCurrentlyConsumer(consumer, providerState)) {
                List({
                        id: providerState.runningVscId,
                        validatorSet: providerState.chainState.currentValidatorSet,
                          sendingTime: providerState.chainState.lastTimestamp
                })
            } else {
                List()
            }
        )
        providerState.with(
            // send VSCPackets to consumers
            "outstandingPacketsToConsumer",
            ConsumerChains.mapBy(
                (consumer) => 
                providerState.outstandingPacketsToConsumer.get(consumer).concat(
                    newSentPacketsPerConsumer.get(consumer)
                )
            )
            ).with(
                // update the sent VSCPackets
                "sentVSCPackets",
                ConsumerChains.mapBy(
                    (consumer) => 
                    providerState.sentVSCPackets.get(consumer).concat(
                        newSentPacketsPerConsumer.get(consumer)
                    )
                )
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
        } else if (currentState.providerState.sentVSCPackets.get(sender).head().id != packet.id) {
            // the packet is not the oldest sentVSCPacket, something went wrong
            Err("Received maturation is not for the oldest sentVSCPacket")
        } else {
            val currentReceivedMaturations = currentState.providerState.receivedMaturations
            val newReceivedMaturations = currentReceivedMaturations.union(Set(packet))
            val newProviderState = currentState.providerState.with(
                "receivedMaturations", newReceivedMaturations
            )
            // prune the sentVSCPacket
            val newSentVSCPacket = currentState.providerState.sentVSCPackets.get(sender).tail()
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

    // removes the oldest outstanding packet (to the given consumer) from the provider.
    // on-chain, this would happen when the packet is acknowledged.
    // only the oldest packet can be removed, since we model ordered channels.
    pure def removeOutstandingPacketFromProvider(currentState: ProtocolState, receiver: Chain): Result = {
        val currentOutstandingPackets = currentState.providerState.outstandingPacketsToConsumer.get(receiver)
        val newOutstandingPackets = currentOutstandingPackets.tail()
        val newProviderState = currentState.providerState.with(
            "outstandingPacketsToConsumer", 
            currentState.providerState.outstandingPacketsToConsumer.set(receiver, newOutstandingPackets)
        )
        val newState = currentState.with(
            "providerState", newProviderState
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

    // Returns whether the consumer has timed out due to the VSCTimeout, and an error message.
    // If the second return is not equal to "", the first return should be ignored.
    // If it is equal to "", the first return will be true if the consumer has timed out and should be dropped,
    // or false otherwise.
    pure def TimeoutDueToVSCTimeout(currentState: ProtocolState, consumer: Chain): (bool, str) =
        // check for errors: the consumer is not running
        if (not(isCurrentlyConsumer(consumer, currentState.providerState))) {
            (false, "Consumer is not currently a consumer - must have 'running' status!")
        } else {
            val providerState = currentState.providerState
            val consumerState = currentState.consumerStates.get(consumer)

            // has a packet been sent on the provider more than VSCTimeout ago, but we have not received an answer since then?
            val sentVSCPackets = providerState.sentVSCPackets.get(consumer)
            val oldestSentVSCPacket = sentVSCPackets.head() // if length is 0, this is undefined, but we check for this before we use it
            if(sentVSCPackets.length() > 0 and oldestSentVSCPacket.sendingTime + VscTimeout < providerState.chainState.lastTimestamp) {
                (true, "")
            } else {
                // no timeout yet, it has not been VscTimeout since that packet was sent
                (false, "")
            }
        }

    // ===================
    // ASSUMPTIONS ON MODEL PARAMETERS
    // ===================

    run UnbondingPeriodPositiveTest =
        UnbondingPeriodPerChain.keys().forall(chain => UnbondingPeriodPerChain.get(chain) > 0)

    run VscTimeoutPositiveTest =
        VscTimeout > 0

    run CcvTimeoutPositiveTest =
        CcvTimeout.keys().forall(chain => CcvTimeout.get(chain) > 0)

    run CcvTimeoutLargerThanUnbondingPeriodTest =
        CcvTimeout.get(PROVIDER_CHAIN) > UnbondingPeriodPerChain.Values().Max()

    run ProviderIsNotAConsumerTest =
        not(ConsumerChains.contains(PROVIDER_CHAIN))

    // ccv timeout contains exactly consumers and provider, no other chains
    run CcvTimeoutKeysTest =
        CcvTimeout.keys() == ConsumerChains.union(Set(PROVIDER_CHAIN))

    // unbonding period contains exactly consumers and provider, no other chains
    run UnbondingPeriodKeysTest =
        UnbondingPeriodPerChain.keys() == ConsumerChains.union(Set(PROVIDER_CHAIN))
}


module CCVDefaultStateMachine {
    // A basic state machine that utilizes the CCV protocol.
    import Time.* from "./Time"
    import CCVTypes.*
    import extraSpells.* from "./extraSpells"

    pure val consumerChains = Set("consumer1", "consumer2", "consumer3")
    pure val chains = consumerChains.union(Set(PROVIDER_CHAIN))
    pure val unbondingPeriods = chains.mapBy(chain => 2 * Week)
    pure val ccvTimeouts = chains.mapBy(chain => 3 * Week)

    pure val nodes = Set("node1", "node2", "node3", "node4", "node5", "node6", "node7", "node8", "node9", "node10")
    pure val InitialValidatorSet = nodes.mapBy(node => 100)

    import CCV(VscTimeout = 5 * Week, CcvTimeout = ccvTimeouts, UnbondingPeriodPerChain = unbondingPeriods, ConsumerChains = consumerChains).*


    var currentState: ProtocolState

    action init: bool = all {
        val providerState = GetEmptyProviderState
        val consumerStates = ConsumerChains.mapBy(chain => GetEmptyConsumerState)
        val providerStateWithConsumers = providerState.with(
            "consumerStatus", 
            ConsumerChains.mapBy(chain => UNUSED)
        ).with(
            "outstandingPacketsToConsumer", 
            ConsumerChains.mapBy(chain => List())
        ).with(
            "sentVSCPackets", 
            ConsumerChains.mapBy(chain => List())
        ).with(
            // set the validator set to be the initial validator set in the history
            "chainState", providerState.chainState.with(
                "votingPowerHistory", List(InitialValidatorSet)
            ).with(
                "currentValidatorSet", InitialValidatorSet
            )
        )
        currentState' = {
            providerState: providerStateWithConsumers,
            consumerStates: consumerStates
        }
    }

    action VotingPowerChange(validator: Node, newVotingPower: int): bool = 
        val result = votingPowerChange(currentState, validator, newVotingPower)
        all {
            result.hasError == false,
            currentState' = result.newState,
        }

    // The receiver receives the next outstanding VSCPacket from the provider.
    // This will time out the consumer if the packet timeout has passed on the receiver.
    action DeliverVSCPacket(receiver: Chain): bool = 
        val resultAndTimeout = deliverPacketToConsumer(currentState, receiver)
        val result = resultAndTimeout._1
        all {
            result.hasError == false,
            currentState' = result.newState,
        }

    // The provider receives the next outstanding VSCMaturedPacket from the sender.
    // This will time out the consumer if the packet timeout has passed on the provider.
    action DeliverVSCMaturedPacket(sender: Chain): bool =
        val resultAndTimeout = deliverPacketToProvider(currentState, sender)
        val result = resultAndTimeout._1
        all {
            result.hasError == false,
            currentState' = result.newState,
        }

    action EndAndBeginBlockForProvider(
        timeAdvancement: Time,
        consumersToStart: Set[Chain],
        consumersToStop: Set[Chain]): bool = 
        val result = endAndBeginBlockForProvider(currentState, timeAdvancement, consumersToStart, consumersToStop)
        all {
            result.hasError == false,
            currentState' = result.newState,
        }

    action EndAndBeginBlockForConsumer(
        chain: Chain,
        timeAdvancement: Time): bool = 
        val result = endAndBeginBlockForConsumer(currentState, chain, timeAdvancement)
        all {
            result.hasError == false,
            currentState' = result.newState,
        }

    run InitTest: bool = { 
        init.then(
            all {
                assert(currentState.providerState.consumerStatus == Map(
                    "consumer1" -> UNUSED,
                    "consumer2" -> UNUSED,
                    "consumer3" -> UNUSED
                )),
                assert(currentState.providerState.outstandingPacketsToConsumer == Map(
                    "consumer1" -> List(),
                    "consumer2" -> List(),
                    "consumer3" -> List()
                )),
                assert(currentState.providerState.sentVSCPackets == Map(
                    "consumer1" -> List(),
                    "consumer2" -> List(),
                    "consumer3" -> List()
                )),
                assert(currentState.consumerStates.keys() == consumerChains),
                assert(currentState.providerState.chainState.votingPowerHistory == List(InitialValidatorSet)),
                assert(currentState.providerState.chainState.currentValidatorSet == InitialValidatorSet),
                assert(currentState.providerState.chainState.lastTimestamp == 0),
                val firstState = currentState // snapshot the first state
                VotingPowerChange("node1", 50).then(all {
                            // ensure that the only change is that the voting power of node1 is changed
                            assert(currentState == firstState.with(
                                "providerState", firstState.providerState.with(
                                    "chainState", firstState.providerState.chainState.with(
                                        "currentValidatorSet", firstState.providerState.chainState.currentValidatorSet.put("node1", 50)
                                    )
                                )
                            )),
                            currentState' = currentState
                        })
                    }
            )
        }

}

// contains test logic for the stateless functions in the CCV module
module CCVLogicTest {
    import CCVTypes.*
    import Time.* from "./Time"
    import extraSpells.* from "./extraSpells"

    pure val consumerChains = Set("sender", "receiver")
    pure val chains = consumerChains.union(Set(PROVIDER_CHAIN))
    pure val unbondingPeriods = chains.mapBy(chain => 2 * Week)
    pure val ccvTimeouts = chains.mapBy(chain => 3 * Week)

    import CCV(VscTimeout = 5 * Week, CcvTimeout = ccvTimeouts, UnbondingPeriodPerChain = unbondingPeriods, ConsumerChains = consumerChains).*

    // negative voting powers give an error
    run VotingPowerNegativeTest =
    {
        votingPowerChange(
            GetEmptyProtocolState,
            "validator",
            -1
        ).hasError
    }

    run VotingPowerOkTest =
    {
        val result = votingPowerChange(
            GetEmptyProtocolState,
            "validator",
            5
        )
        not(result.hasError) and
        result.newState.providerState.chainState.currentValidatorSet.keys().contains("validator") and
        result.newState.providerState.chainState.currentValidatorSet.get("validator") == 5
    }

    // validators that get zero voting power are removed
    run VotingPowerZeroTest =
    {
        val tmpResult = votingPowerChange(
            GetEmptyProtocolState,
            "validator",
            5
        )
        val finalResult = votingPowerChange(
            tmpResult.newState,
            "validator",
            0
        )
        not(finalResult.hasError) and
        not(finalResult.newState.providerState.chainState.currentValidatorSet.keys().contains("validator"))
    }


    // make sure that VotingPowerChange ONLY changes the current validator set, not the history
    run VotingPowerChangeDoesNotChangeHistoryTest =
    {
        val result = votingPowerChange(
            GetEmptyProtocolState,
            "validator",
            0
        )
        not(result.hasError) and
        result.newState.providerState.chainState.votingPowerHistory == List()
    }

    // add a packet on the consumer
    pure val DeliverPacketToProviderHappyPathTest_testState = _DeliverPacketToProvider_TestState.with(
        "consumerStates", _DeliverPacketToProvider_TestState.consumerStates.put(
            "sender", _DeliverPacketToProvider_TestState.consumerStates.get("sender").with(
                "outstandingPacketsToProvider", List({
                    id: 0,
                    sendingTime: 0
                })
            )
        )
    ).with(
        // put an entry into sentVSCPacket on the provider that corresponds to the packet we put on the consumer
        "providerState", _DeliverPacketToProvider_TestState.providerState.with(
            "sentVSCPackets", _DeliverPacketToProvider_TestState.providerState.sentVSCPackets.put(
                "sender", List({
                    id: 0,
                    validatorSet: _DeliverPacketToProvider_TestState.providerState.chainState.currentValidatorSet,
                    sendingTime: 0
                })
            )
        )
    )

    pure val DeliverPacketToProviderHappyPathTest_resultAndTimeout = deliverPacketToProvider(DeliverPacketToProviderHappyPathTest_testState, "sender")

    // test is split to be easier to pinpoint which assertion failed
    run DidNotTimeOut_DeliverPacketToProviderHappyPathTest =
    {
        val result = DeliverPacketToProviderHappyPathTest_resultAndTimeout._1
        val timeout = DeliverPacketToProviderHappyPathTest_resultAndTimeout._2
        not(result.hasError) and
        not(timeout)
    }

    run StateModificationOK_DeliverPacketToProviderHappyPathTest =
    {
        val result = DeliverPacketToProviderHappyPathTest_resultAndTimeout._1
        val timedOut = DeliverPacketToProviderHappyPathTest_resultAndTimeout._2
        val newProviderState = result.newState.providerState
        val newConsumerState = result.newState.consumerStates.get("sender")
        not(result.hasError) and
        newProviderState.receivedMaturations.size() == 1 and
        newConsumerState.outstandingPacketsToProvider.length() == 0
    }

    // add a packet on the consumer
    pure val DeliverPacketToProviderTimeoutTest_testState = DeliverPacketToProviderHappyPathTest_testState.with(
            "providerState", DeliverPacketToProviderHappyPathTest_testState.providerState.with(
                "chainState", DeliverPacketToProviderHappyPathTest_testState.providerState.chainState.with(
                    // set the timestamp to be after the timeout
                    "lastTimestamp", CcvTimeout.get("sender") + 1
                )
            )
        )

    pure val DeliverPacketToProviderTimeoutTest_resultAndTimeout = deliverPacketToProvider(DeliverPacketToProviderTimeoutTest_testState, "sender")

    run DidTimeOut_DeliverPacketToProviderTimeoutTest =
    {
        val result = DeliverPacketToProviderTimeoutTest_resultAndTimeout._1
        val timedOut = DeliverPacketToProviderTimeoutTest_resultAndTimeout._2
        val newProviderState = result.newState.providerState
        val newConsumerState = result.newState.consumerStates.get("sender")
        not(result.hasError) and
        timedOut
    }

    run StateModificationOK_DeliverPacketToProviderTimeoutTest =
    {
        val result = DeliverPacketToProviderTimeoutTest_resultAndTimeout._1
        val timedOut = DeliverPacketToProviderTimeoutTest_resultAndTimeout._2
        val newProviderState = result.newState.providerState
        val newConsumerState = result.newState.consumerStates.get("sender")
        not(result.hasError) and
        newProviderState.receivedMaturations.size() == 0 and
        newConsumerState.outstandingPacketsToProvider.length() == 0 and
        newProviderState.consumerStatus.get("sender") == STOPPED
    }

    run ConsumerStatusMapHappyPathTest = 
    {
        val currentConsumerStatusMap = Map(
            "chain1" -> UNUSED,
            "chain2" -> RUNNING,
            "chain3" -> STOPPED
        )
        val res = getNewConsumerStatusMap(
            currentConsumerStatusMap,
            Set("chain1"),
            Set("chain2")
        )
        res._2 == "" and
        res._1.get("chain1") == RUNNING and
        res._1.get("chain2") == STOPPED and
        res._1.get("chain3") == STOPPED
    }

    run ConsumerStatusMapAlreadyRunningTest =
    {
        val currentConsumerStatusMap = Map(
            "chain1" -> UNUSED,
            "chain2" -> RUNNING,
            "chain3" -> STOPPED
        )
        val res = getNewConsumerStatusMap(
            currentConsumerStatusMap,
            Set("chain2"),
            Set("chain3")
        )
        res._2 == "Cannot start a consumer that is already running"
    }

    run ConsumerStatusMapAlreadyStoppedTest =
    {
        val currentConsumerStatusMap = Map(
            "chain1" -> UNUSED,
            "chain2" -> RUNNING,
            "chain3" -> STOPPED
        )
        val res = getNewConsumerStatusMap(
            currentConsumerStatusMap,
            Set("chain1"),
            Set("chain3")
        )
        res._2 == "Cannot stop a consumer that is not running"
    }

    run ChainBothInStartAndStopTest =
    {
        val currentConsumerStatusMap = Map(
            "chain1" -> UNUSED,
            "chain2" -> RUNNING,
            "chain3" -> STOPPED
        )
        val res = getNewConsumerStatusMap(
            currentConsumerStatusMap,
            Set("chain1"),
            Set("chain1")
        )
        res._2 == "Cannot start and stop a consumer at the same time"
    }
}
