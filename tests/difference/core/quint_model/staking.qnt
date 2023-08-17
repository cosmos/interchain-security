module ccv {
    import extraSpells.* from "./extraSpells"

    // Things that are not modelled:
    // * Reward distribution
    
    // TYPE DEFINITIONS
    type Chain = str
    type Validator = {
        identifier: str,
        // for simplciity, voting power is equal to amount of tokens
        votingPower: int
    }
    type Height = int
    type Timestamp = int

    type Infraction = 
        {
            validator: Validator,
            infractionType: str,
            // slash fraction in percent, i.e. 80 means 80%
            slashFraction: int,
            // the height at which the infraction was committed
            infractionHeight: Height,
            // the timestamp at which the infraction was committed
            infractionTime: Timestamp,
            // the chain on which the infraction was committed
            originChain: Chain,
        }

    type Block = 
        {
            validatorSet: Set[Validator],
            blockHeight: Height,
            blockTime: Timestamp,
            chain: Chain,
            // Infrations comitted on this chain in this block.
            comittedInfractions: Set[Infraction],
            // Evidence received by this chain in this block.
            receivedEvidence: Set[Infraction] // only used on the provider
        }

    type Slash = 
        {
            validator: Validator,
            slashAmount: int,
            slashHeight: Height,
            slashTime: Timestamp,
            chain: Chain,
            infraction: Infraction
        }


    // MODEL PARAMETERS
    const UnbondingPeriod: int

    // MODEL STATE

    // The singular provider chain.
    var providerChain: Chain

    // The set of (possible) consumer chains that are being tracked.
    var chains: Set[Chain]

    // Stores, for each chain, the list of blocks over its entire existence.
    // Each height should occur at most once, and no height should be skipped.
    // Blocks should be ordered by height in descending order.
    var blockHistories: Chain -> List[Block]
    
    // Stores, for each chain, whether it is currently a consumer chain.
    var consumerStatus: Chain -> bool

    var slashes: Set[Slash]

    // UTILITY FUNCTIONS
    def getCurrentHeight(chain: Chain): Height = {
        blockHistories.get(chain).head().blockHeight
    }

    def getLatestBlock(chain: Chain): Block = {
        blockHistories.get(chain).head()
    }

    def isConsumer(chain: Chain): bool = {
        consumerStatus.get(chain)
    }

    def wasValidatorSetOnProvider(validatorSet: Set[Validator]): bool = {
        blockHistories.get(providerChain).toSet().exists(
            block => block.validatorSet == validatorSet
        )
    }

    // PROPERTIES

    // Every validator set on any consumer chain MUST either be or
    // have been a validator set on the provider chain.
    val ValidatorSetReplication: bool = 
        chains.filter(chain => chain.isConsumer()).forall(
            chain => chain.getLatestBlock().validatorSet.wasValidatorSetOnProvider()
        )

    // TODO: This is extremely convoluted, maybe coming later?
    val BondBasedConsumerVotingPower: bool =
        true

    // If a validator val commits an infraction, with a slashing fraction of sf,
    // on a consumer chain cc at a block height hi,
    // then any evidence of misbehavior that is received by cc at height he,
    // such that ts(he) < ts(hi) + UnbondingPeriod, MUST results in exactly the amount of tokens
    // sf*Token(Power(cc,hi,val)) to be slashed on the provider chain.
    // Furthermore, val MUST NOT be slashed more than once for the same misbehavior.
    val SlashableConsumerMisbehaviour: bool =
        val latestProviderBlock = providerChain.getLatestBlock()
        latestProviderBlock.receivedEvidence.forall(
            // for each evidence the provider chain received
            evidence => 
                // if the evidence is received before it is outdated
                (evidence.infractionTime < latestProviderBlock.blockTime - UnbondingPeriod)
                    implies
                // the provider needs to slash the validator
                val expectedSlash =
                    {
                        validator: evidence.validator,
                        // the amount depends on the voting power during the infraction
                        slashAmount: evidence.validator.votingPower * evidence.slashFraction,
                        slashHeight: latestProviderBlock.blockHeight,
                        slashTime: latestProviderBlock.blockTime,
                        chain: providerChain,
                        infraction: evidence
                    }
                slashes.exists(slash => slash == expectedSlash)
        )

        val ValidatorUpdateInclusion: bool =
            true

}