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
            sentVSCPackets: Chain -> Set[VSCPacket],

            // a mapping from (chainId, vscId) tuples to the timestamps of sent VSCPackets.
            vscSendTimestamps: (Chain, VSCId) -> Time,

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
            vscSendTimestamps: Map(),
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
    const CcvTimeoutPeriod: Chain -> int

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

    // Delivers the next queued VSCPacket from the provider chain to a consumer chain.
    // Only argument is the consumer chain, to which the packet will be delivered.
    pure def deliverPacketToConsumer(currentState: ProtocolState, receiver: Chain): Result = {
        if (not(isCurrentlyConsumer(receiver, currentState.providerState))) {
            Err("Receiver is not currently a consumer - must have 'running' status!")
        } else if (length(currentState.providerState.outstandingPacketsToConsumer.get(receiver)) == 0) {
            Err("No outstanding packets to deliver")
        } else {
            val packet = currentState.providerState.outstandingPacketsToConsumer.get(receiver).head()
            val result = recvPacketOnConsumer(currentState, receiver, packet)
            val tmpState = result.newState
            if (result.hasError) {
                Err(result.error.message)
            } else {
                val result2 = removeOutstandingPacketFromProvider(tmpState, receiver)
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
        timeAdvancement: Time,
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

    // Returns whether the consumer has timed out, and an error message.
    // If the second return is not equal to "", the first return should be ignored.
    // If it is equal to "", the first return will be true if the consumer has timed out and should be dropped,
    // or false otherwise.
    def consumerTimedOut(currentState: ProtocolState, consumer: Chain): (bool, str) =
        // check for errors: the consumer is not running
        if (not(isCurrentlyConsumer(consumer, currentState.providerState))) {
            (false, "Consumer is not currently a consumer - must have 'running' status!")
        } else {
            val providerState = currentState.providerState
            val consumerState = currentState.consumerStates.get(consumer)

            // has a packe from provider to consumer timed out?
            val outstandingPacketsToConsumer = providerState.outstandingPacketsToConsumer.get(consumer)
            val providerToConsumerPacketTimedOut = outstandingPacketsToConsumer.head().sendingTime +
                CcvTimeoutPeriod.get(PROVIDER_CHAIN) <= consumerState.chainState.lastTimestamp

            // has a packet from consumer to provider timed out?
            val outstandingPacketsToProvider = consumerState.outstandingPacketsToProvider
            val consumerToProviderPacketTimedOut = outstandingPacketsToProvider.head().sendingTime +
                CcvTimeoutPeriod.get(consumer) <= providerState.chainState.lastTimestamp



            (providerToConsumerPacketTimedOut, "")
        }
        
        // // either a package from provider to consumer has timed out
        // currentState..get(consumer).select(
        //     packet => packet.timeout <= curChainTimes.get(consumer)
        // ).length() > 0,
        // // or a package from consumer to provider has timed out
        // outstandingPacketsToProvider.get(consumer).select(
        //     packet => packet.timeout <= curChainTimes.get(ProviderChain)
        // ).length() > 0,
        // // or the inactivity timeout has passed since a VSCPacket was sent to the consumer, but the
        // // provider has not received a VSCMaturedPacket for it
        // val packetsWithoutResponse = sentVSCPackets.get(consumer).filter( // get packets without response
        //     packet => 
        //     not(receivedMaturations.exists(
        //         maturedPacket => maturedPacket.id == packet.id
        //     ))
        // )
        // // among those, get packets where inactivity timeout has passed
        // packetsWithoutResponse.filter(
        //     packet => 
        //     val sentAt = curChainTimes.get(ProviderChain) - PacketTimeout // compute when the packet was sent
        //     val timesOutAt = sentAt + InactivityTimeout // compute when the packet times out
        //     timesOutAt <= curChainTimes.get(ProviderChain)
        // ).size() > 0

    // ===================
    // ASSUMPTIONS ON MODEL PARAMETERS
    // ===================

    // the unbonding period is positive
    run UnbondingPeriodPositiveTest =
        UnbondingPeriodPerChain.keys().forall(chain => UnbondingPeriodPerChain.get(chain) > 0)

    // the VSC timeout is positive
    run VscTimeoutPositiveTest =
        VscTimeout > 0

    // the CCV timeout is positive
    run CcvTimeoutPositiveTest =
        CcvTimeoutPeriod.keys().forall(chain => CcvTimeoutPeriod.get(chain) > 0)

    // ccv timeout on the provider **must** be larger than unbonding period on each chain
    run CcvTimeoutLargerThanUnbondingPeriodTest =
        CcvTimeoutPeriod.get(PROVIDER_CHAIN) > UnbondingPeriodPerChain.Values().Max()

    // the provider chain is not a consumer chain
    run ProviderNotConsumerTest =
        not(ConsumerChains.contains(PROVIDER_CHAIN))

    // ccv timeout contains only consumers and provider, no other chains
    run CcvTimeoutSubsetTest =
        CcvTimeoutPeriod.keys().forall(chain => ConsumerChains.contains(chain) or chain == PROVIDER_CHAIN)

    // unbonding period contains consumers and provider, no other chains
    def UnbondingPeriodInv = UnbondingPeriodPerChain.keys() == ConsumerChains.add(PROVIDER_CHAIN)

    
}

// A basic state machine that utilizes the CCV protocol.
// Still leaves constants unassigned, just defines the state machine logic in general,
// i.e. regardless of how many chains there are, what the unbonding periods are, etc.
module CCVStatemachinLogic {
    import Time.* from "./Time"
    import CCV as CCV
    import CCVTypes.*

    var currentState: ProtocolState

    action init: bool = all {
        val providerState = GetEmptyProviderState
        val consumerStates = CCV::ConsumerChains.mapBy(chain => GetEmptyConsumerState)
        currentState' = {
            providerState: providerState,
            consumerStates: consumerStates
        }
    }

    action votingPowerChanges(validator: Node, amount: int): bool = 
        val result = CCV::votingPowerChange(currentState, validator, amount)
        all {
        result.hasError == false,
        currentState' = result.newState,
    }

    // The receiver receives the next outstanding VSCPacket from the provider.
    action DeliverVSCPacket(receiver: Chain): bool = 
        val result = CCV::deliverPacketToConsumer(currentState, receiver)
        all {
            result.hasError == false,
            currentState' = result.newState,
        }

    action DeliverVSCMaturedPacket(sender: Chain): bool =
        val result = CCV::deliverPacketToProvider(currentState, sender)
        all {
            result.hasError == false,
            currentState' = result.newState,
        }

    action EndAndBeginBlockForProvider(
        timeAdvancement: Time,
        consumersToStart: Set[Chain],
        consumersToStop: Set[Chain]): bool = 
        val result = CCV::endAndBeginBlockForProvider(currentState, timeAdvancement, consumersToStart, consumersToStop)
        all {
            result.hasError == false,
            currentState' = result.newState,
        }

    action EndAndBeginBlockForConsumer(
        chain: Chain,
        timeAdvancement: Time): bool = 
        val result = CCV::endAndBeginBlockForConsumer(currentState, chain, timeAdvancement)
        all {
            result.hasError == false,
            currentState' = result.newState,
        }
}

module CCVDefaultStateMachine {
    // A basic state machine that utilizes the CCV protocol.
    import Time.* from "./Time"
    import CCVTypes.*
    import extraSpells.* from "./extraSpells"

    pure val consumerChains = Set("consumer1", "consumer2", "consumer3")
    pure val chains = consumerChains.add(PROVIDER_CHAIN)
    pure val unbondingPeriods = chains.mapBy(chain => 2 * Week)
    pure val ccvTimeouts = chains.mapBy(chain => 3 * Week)

    import CCV(VscTimeout = 5 * Week, CcvTimeoutPeriod = unbondingPeriods, UnbondingPeriodPerChain = unbondingPeriods, ConsumerChains = chains).*
}
