module ccv {
    import extraSpells.* from "./extraSpells"

    // Things that are not modelled:
    // * Reward distribution
    // * Starting/Stopping chains during execution
    // * Slashes
    
    // TYPE DEFINITIONS
    type Node = str
    type Chain = str
    type ValidatorSet = Node -> int
    type Height = int
    type Timestamp = int

    // --PACKETS
    type VSCPacket =
        {   
            // the identifier for this packet
            id: int,
            // the new validator set. in the implementation, this would be a list of validator updates
            validatorSet: ValidatorSet
        }

    type VSCMaturedPacket = 
        {
            // the id of the VSCPacket that matured
            id: int
        }
    
    // MODEL PARAMETERS
    // length of the unbonding period on each chain
    const UnbondingPeriod: Chain -> int

    // set of identifiers of potential nodes
    const Nodes: Set[Node]

    // the set of consumer chains
    const ConsumerChains: Set[Chain]

    // The singular provider chain.
    const ProviderChain: Chain

    pure val chains = ConsumerChains.union(Set(ProviderChain))

    // the time until a packet times out
    const PacketTimeout: int

    // the time until a consumer chain is dropped by the provider due to inactivity
    const InactivityTimeout: int


    // MODEL STATE
    // --SHARED STATE

    // Stores, for each chain, the list of voting powers that corresponded to voting powers 
    // at blocks over its entire existence.
    // Voting powers should be ordered by recency in descending order.
    var votingPowerHistories: Chain -> List[ValidatorSet]

    // the current validator set on each chain.
    // this will be included in the next block, but might not be final yet,
    // e.g. there may be more modifications in the current block.
    var runningValidatorSet: Chain -> ValidatorSet

    // the current timestamp for each chain
    var curChainTimes: Chain -> Timestamp

    // stores, for each chain, its current status -
    // unused, running, or stopped
    var consumerStatus: Chain -> str

    // --CHANNELS
    // Stores, for each consumer chain, the list of packets that have been sent to the provider chain
    // and have not been received yet.
    var outstandingPacketsToProvider: Chain -> List[VSCMaturedPacket]

    // Stores, for each consumer chain, the list of packets that have been sent to the consumer chain
    // and have not been received yet.
    var outstandingPacketsToConsumer: Chain -> List[VSCPacket]


    // --CONSUMER STATE
    // Stores the maturation times for VSCPackets received by consumers
    var maturationTimes: Chain -> (VSCPacket -> Timestamp)

    // --PROVIDER STATE
    // the set of VSCMaturedPackets received by the provider chain
    var receivedMaturations: Set[VSCMaturedPacket]


    // UTILITY FUNCTIONS & ACTIONS
    def wasValidatorSetOnProvider(validatorSet: ValidatorSet): bool = {
        votingPowerHistories.get(ProviderChain).toSet().exists(
            historicalValSet => historicalValSet == validatorSet
        )
    }

    def getCurrentValidatorSet(chain: Chain): ValidatorSet = 
        votingPowerHistories.get(chain).head()

    def getUpdatedValidatorSet(oldValidatorSet: ValidatorSet, validator: Node, newVotingPower: int): ValidatorSet =
        if (newVotingPower > 0) 
        oldValidatorSet.set(validator, newVotingPower)
        else
        oldValidatorSet.mapRemove(validator)

    // utility action that leaves all provider state untouched
    action PROVIDER_NOOP(): bool = 
        all {
            receivedMaturations' = receivedMaturations,
        }

    // utility action that leaves all consumer state untouched
    action CONSUMER_NOOP(): bool = 
        all {
            maturationTimes' = maturationTimes,
        }
    

    // MODEL ACTIONS

    // the power of a validator on the provider chain is changed to the given amount. We do not care how this happens,
    // e.g. via undelegations, or delegations, ...
    action votingPowerChange(validator: Node, amount: int): bool =
        // for the provider chain, we need to adjust the voting power history
        // by adding a new set
        all {
            amount >= 0,
            val newValidatorSet = getCurrentValidatorSet(ProviderChain).getUpdatedValidatorSet(validator, amount)
            // set the running validator set on the provider chain, but don't update the history yet
            runningValidatorSet' = runningValidatorSet.set(ProviderChain, newValidatorSet),
            // no packets are sent yet, these are only sent on endAndBeginBlock
            outstandingPacketsToConsumer' = outstandingPacketsToConsumer,
            outstandingPacketsToProvider' = outstandingPacketsToProvider,
            receivedMaturations' = receivedMaturations,
            CONSUMER_NOOP,
            // voting power history is only updated on endAndBeginBlock
            votingPowerHistories' = votingPowerHistories,
        }

    // deliver the next outstanding packet from the consumer to the provider.
    // since this model assumes a single provider chain, this just takes a single chain as argument.
    action recvPacketOnProvider(consumer: Chain): bool = all {
        // ensure there is a packet to be received
        outstandingPacketsToProvider.get(consumer).length() > 0,
        // remove packet from outstanding packets
        val newPacketQueue = outstandingPacketsToProvider.get(consumer).tail()
        outstandingPacketsToProvider' = outstandingPacketsToProvider.set(consumer, newPacketQueue),
        // register the packet as received
        val maturedPacket = outstandingPacketsToProvider.get(consumer).head()
        receivedMaturations' = receivedMaturations.add(maturedPacket),
        CONSUMER_NOOP,
        outstandingPacketsToConsumer' = outstandingPacketsToConsumer,
        votingPowerHistories' = votingPowerHistories,
        // no validator set changes are made
        runningValidatorSet' = runningValidatorSet,
    }

    // deliver the next outstanding packet from the provider to the consumer.
    // since this model assumes a single provider chain, this just takes a single chain as argument.
    action recvPacketOnConsumer(consumer: Chain): bool = all {
        // ensure there is a packet to be received
        outstandingPacketsToConsumer.get(consumer).length() > 0,
        // remove packet from outstanding packets
        val newPacketQueue = outstandingPacketsToConsumer.get(consumer).tail()
        outstandingPacketsToConsumer' = outstandingPacketsToConsumer.set(consumer, newPacketQueue),
        val packet = outstandingPacketsToConsumer.get(consumer).head()
        all {
            // update the running validator set, but not the history yet,
            // as that only happens when the next block is started
            runningValidatorSet' = runningValidatorSet.set(consumer, packet.validatorSet),
            // add the new packet and store its maturation time
            val newMaturationTimes = maturationTimes.get(consumer).set(packet, curChainTimes.get(consumer) + UnbondingPeriod.get(consumer))
            maturationTimes' = maturationTimes.set(consumer, newMaturationTimes)
        },
        PROVIDER_NOOP,
        votingPowerHistories' = votingPowerHistories,
        outstandingPacketsToProvider' = outstandingPacketsToProvider,
    }

    // ends the current block and starts the next block for a given chain.
    action endAndBeginBlock(chain: Chain): bool = any {
        all {
          chain == ProviderChain,
          endAndBeginBlockForProvider,
        },
        all {
            chain != ProviderChain,
            endAndBeginBlockForConsumer(chain),
        }
    }

    // gets the updated history for the current chain when ending a block, i.e. the
    // running validator set is added to the history if different from the last one.
    def getUpdatedHistory(chain: Chain): List[ValidatorSet] =
        // update voting power history if the validator set changed
        val newValidatorSet = runningValidatorSet.get(ProviderChain)
        val oldValidatorSet = votingPowerHistories.get(ProviderChain).head()
        if (newValidatorSet != oldValidatorSet) 
            votingPowerHistories.get(ProviderChain).prepend(newValidatorSet)
        else
            votingPowerHistories.get(ProviderChain)


    action endAndBeginBlockForProvider(): bool = all {
        // update the voting power history
        votingPowerHistories' = votingPowerHistories.set(ProviderChain, getUpdatedHistory(ProviderChain)),
        // the running validator set is now for sure the current validator set,
        // so start with it in the next block
        runningValidatorSet' = runningValidatorSet,
        // send VSCPackets to consumers
        outstandingPacketsToConsumer' = 
            // if running validator set is not equal to the last one in the history
            if (runningValidatorSet.get(ProviderChain) != votingPowerHistories.get(ProviderChain).head())
                // then send a packet to each consumer
                outstandingPacketsToConsumer.keys().mapBy(
                    (consumer) => 
                    val packetQueue = outstandingPacketsToConsumer.get(consumer)
                    packetQueue.append(
                        {
                            id: packetQueue.length(),
                            validatorSet: runningValidatorSet.get(ProviderChain)
                        }
                    )
                )
            else
                // otherwise, don't send any packets
                outstandingPacketsToConsumer,
        CONSUMER_NOOP,
        // no packets are sent to the provider
        outstandingPacketsToProvider' = outstandingPacketsToProvider,
        // do not receive any maturations
        receivedMaturations' = receivedMaturations,
    }

    action endAndBeginBlockForConsumer(consumer: Chain): bool = all {
        ConsumerChains.contains(consumer),
        // update the voting power history
        votingPowerHistories' = votingPowerHistories.set(consumer, getUpdatedHistory(consumer)),
        // the running validator set is now for sure the current validator set,
        // so start with it in the next block
        runningValidatorSet' = runningValidatorSet,
        // compute mature packets whose maturation time has passed
        val maturedPackets = maturationTimes.get(consumer).keys().filter(
            packet => 
            val maturationTime = maturationTimes.get(consumer).get(packet)
            maturationTime <= curChainTimes.get(consumer)
        )
        all {
            // remove matured packets from the maturation times
            maturationTimes' = maturationTimes.set(consumer, maturationTimes.get(consumer).mapRemoveAll(maturedPackets)),
            // send matured packets
            outstandingPacketsToProvider' = outstandingPacketsToProvider.set(
                consumer, 
                // construct VSCMaturedPackets from the matured VSCPackets
                outstandingPacketsToProvider.get(consumer).concat(
                    maturedPackets.map(packet => {id: packet.id}).toList()
                )
            )
        },
        PROVIDER_NOOP,
        // no packets are sent to consumer or received by it
        outstandingPacketsToConsumer' = outstandingPacketsToConsumer,
    }

    // the timestamp for each chain is advanced nondeterministically
    action advanceTimestamps(): bool =
        curChainTimes' = curChainTimes.keys().mapBy(
            (chain) => 
            nondet advancement = oneOf(0.to(100))
            curChainTimes.get(chain) + advancement
        )

    // each consumer chain may nondeterministically advance in the order
    // unused -> initializing -> running -> stopped
    // some events may necessitate a transition, e.g. timeouts
    action AdvanceConsumers: bool = 
        consumerStatus' = consumerStatus.keys().mapBy(
            (chain) => 
            val curStatus = consumerStatus.get(chain)
            // if the current status is unused, it may transition to running
            if (curStatus == "unused") {
                nondet transition = oneOf(0.to(1))
                if (transition == 0)
                {
                    "running"
                } else {
                    "unused"
                }
            }
            else if (curStatus == "running") {
                // the chain may transition to stopped.
                // it is *forced* to stop if a packet timed out,
                // or if the inactivity timeout has passed
            } else {
                "unused"
            }

            // if the current status is initializing, it may transition to running
        )


    action step: bool = 
    all {  
        // timestamps can be advanced in each step
        advanceTimestamps,  
        any {
            nondet node = oneOf(Nodes)
            nondet amount = oneOf(1.to(10))
            votingPowerChange(node, amount),
            recvPacketOnProvider(oneOf(ConsumerChains)),
            recvPacketOnConsumer(oneOf(ConsumerChains)),
            nondet chain = oneOf(chains)
            endAndBeginBlock(chain),
        }
    }

    // PROPERTIES

    // Every validator set on any consumer chain MUST either be or
    // have been a validator set on the provider chain.
    val ValidatorSetReplication: bool = 
        chains.forall(
            chain => chain.getCurrentValidatorSet().wasValidatorSetOnProvider()
        )
}