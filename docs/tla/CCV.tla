--------------------------- MODULE CCV ---------------------------
(*
 * Modeling voting power relay between provider- and consumer chains in ICS.
 *
 * Simplifications:
 *   - We only track voting power, not bonded tokens
 *   - CCV channel creation is atomic and never fails/times out.
 *   - No new consumers join midway.
 *   - Block height is not modeled.
 * 
 * Jure Kukovec, 2022
 *)

EXTENDS Integers, Sequences, Apalache, typedefs

CONSTANT 
  \* The set of all nodes, which may take on a validator role.
  \* node \in Nodes is a validator <=> node \in DOMAIN votingPowerRunning
  \* @type: Set($node);
  Nodes, 
  \* The set of all consumer chains. Consumers may be removed 
  \* during execution, but not added.
  \* @type: Set($chain);
  ConsumerChains, 
  \* Time that needs to elapse, before a received VPC is considered
  \* mature on a chain.
  \* @type: $time;
  MaturityDelay,
  \* Time that needs to elapse, before a message is considered to have
  \* timed out (resulting in the removal of the related consumer chain).
  \* @type: $time;
  Timeout,
  \* Maximal time by which clocks are assumed to differ from the provider chain.
  \* Since consumer chains don't communicate, we don't care about 
  \* drift between tow consumers (though it's implicitly less than MaxDrift, if
  \* each differs from the provider chain by at most MaxDrift).
  \* The specification doesn't force clocks to maintain bounded drift, 
  \* but the invariants are only verified in cases where clocks never drift too far.
  \* @type: $time;
  MaxDrift

\* Timeout must be more than MaturityDelay, otherwise VPCs would
\* never have the opportunity to mature.
ASSUME (Timeout > MaturityDelay)

\* Provider chain only
VARIABLES
  \* Snapshots of the voting power on the provider chain, at the times
  \* when a VPC packet was sent.
  \* t \in DOMAIN votingPowerHist <=> VPC packet sent at time t
  \* @type: $time -> $votingPowerOnChain;
  votingPowerHist,
  \* Current voting power on the provider chain. 
  \* @type: $votingPowerOnChain;
  votingPowerRunning,
  \* Current set of active consumers. Inactive (by timeout) are dropped after
  \* each transition. May also drop arbitrarily.
  \* @type: Set($chain);
  activeConsumers,
  \* The set of VPC packet acknowledgements sent by consumer chains to the
  \* provider chain.
  \* @type: Set($ack);
  acks

\* Consumer chains or both
VARIABLES 
  \* Representation of the current voting power, as understood by consumer chains.
  \* Because consumer chains may not arbitrarily modify their own voting power,
  \* but must instead update in accordance to VPC packets received from the
  \* provider, it is sufficient to only track the last received packet.
  \* The voting power on chain c is then equal to votingPowerHist[votingPowerReferences[c]].
  \* @type: $chain -> $time;
  votingPowerReferences,
  \* The queues of VPC packets, waiting to be received by consumer chains.
  \* Note that a packet being placed in the channel is not considered 
  \* received by the consumer, until the receive-action is taken.
  \* @type: $chain -> Seq($packet);
  ccvChannels,
  \* The current times of all chains (including the provider).
  \* @type: $chain -> $time;
  currentTimes,
  \* Bookkeeping of maturity times for received VPC packets.
  \* A consumer may only acknowledge a packet (i.e. notify the provider) after
  \* its local time exceeds the time designated in maturityTimes.
  \* For each consumer chain c, and VPC packet t sent by the provider,
  \* a) t \in DOMAIN maturityTimes[c] <=> c has received packet t 
  \* b) if t \in DOMAIN maturityTimes[c], then the acknowledge-action for t is 
  \*    guarded by currentTimes[c] >= maturityTimes[c][t]
  \* @type: $chain -> $packet -> $time;
  maturityTimes

\* Bookkeeping
VARIABLES 
  \* Name of last action, for debugging
  \* @type: Str;
  lastAction,
  \* VPC flag; Voting power may be considered to have changed, even if 
  \* the (TLA) value of votingPowerRunning does not (for example, due to a sequence
  \* of delegations and un-delegations, with a net 0 change in voting power).
  \* We use this flag to determine whether it is necessary to send a VPC packet.
  \* @type: Bool;
  votingPowerHasChanged,
  \* Invariant flag, TRUE iff clocks never drifted too much
  \* @type: Bool;
  boundedDrift

\* Helper tuples for UNCHANGED syntax
\* We don't track activeConsumers and lastAction in var tuples, because
\* they change each round.

providerVars ==
  << votingPowerHist, votingPowerRunning, acks >>

consumerVars ==
  << votingPowerReferences, ccvChannels, currentTimes, maturityTimes >>

\* @type: <<Bool, Bool>>;
bookkeepingVars == 
  << votingPowerHasChanged, boundedDrift >>


(*** NON-ACTION DEFINITIONS ***)

\* Some value not in Nat, for initialization
UndefinedTime == -1

\* Provider chain ID, assumed to be distinct from all consumer chain IDs
ProviderChain == "provider_OF_C"

\* Some value not in [Nodes -> Nat], for initialization
UndefinedPower == [node \in Nodes |-> -1]

\* All chains, including the provider. Used for the domain of shared
\* variables, e.g. currentTimes
Chains == ConsumerChains \union {ProviderChain}

\* Takes parameters, so primed and non-primed values can be passed
\* @type: ($chain, Seq($packet), $time, $time, $packet -> $time) => Bool;
PacketTimeoutForConsumer(c, channel, consumerT, providerT, maturity) == 
  \* Option 1: Timeout on reception
  \//\ Len(channel) /= 0
    \* Head is always the oldest packet, so if there is a timeout for some packet, 
    \* there must be one for Head too
    /\ consumerT > Head(channel) + Timeout 
  \* Option 2: Timeout on acknowledgement
  \/ \E packet \in DOMAIN maturity: 
    \* Note: Reception time = maturity[packet] - MaturityDelay
    /\ providerT + MaturityDelay > maturity[packet] + Timeout
    \* Not yet acknowledged
    /\ \A ack \in acks:
      \/ ack.chain /= c
      \/ ack.packetTime /= packet

\* Because we're not using functions with fixed domains, we can't use EXCEPT.
\* Thus, we need a helper method for domain-extension.
\* @type: (a -> b, a, b) => a -> b;
ExtendFnBy(f, k, v) ==
  [ 
    x \in DOMAIN f \union {k} |->
      IF x = k
      THEN v
      ELSE f[x]
  ]

\* Packets are set at unique times, monotonically increasing, the last
\* one is just the max in the votingPowerHist domain.
LastPacketTime == 
  LET Max2(a,b) == IF a >= b THEN a ELSE b IN
  ApaFoldSet(Max2, -1, DOMAIN votingPowerHist)

\* @type: ($chain, $time, $time) => $ack;
Ack(c, packetT, ackT) == 
  [chain |-> c, packetTime |-> packetT, ackTime |-> ackT]

\* @type: (Int, Int) => Int;
Delta(a,b) == IF a > b THEN a - b ELSE b - a

\* @type: (a -> Int, Set(a), Int) => Bool;
BoundedDeltas(fn, dom, bound) ==
  /\ dom \subseteq DOMAIN fn
  /\ \A v1, v2 \in dom:
    Delta(fn[v1], fn[v2]) <= bound

(*** ACTIONS ***)

Init == 
  /\ votingPowerHist = [t \in {} |-> UndefinedPower]
  /\ \E initValidators \in SUBSET Nodes:
    /\ initValidators /= {}
    /\ votingPowerRunning \in [initValidators -> Nat]
    /\ \A v \in initValidators: votingPowerRunning[v] > 0
  /\ activeConsumers = ConsumerChains
  /\ acks = {}
  /\ votingPowerReferences = [chain \in ConsumerChains |-> UndefinedTime]
  /\ ccvChannels = [chain \in ConsumerChains |-> <<>>]
  /\ currentTimes = [c \in Chains |-> 0]
  /\ maturityTimes = [c \in ConsumerChains |-> [t \in {} |-> UndefinedTime]]
  /\ votingPowerHasChanged = FALSE
  /\ boundedDrift = TRUE
  /\ lastAction = "Init"

\* We combine all (un)delegate actions, as well as (un)bonding actions into an
\* abstract VotingPowerChange.
\* Since VPC packets are sent at most once at the end of each block,
\* the granularity wouldn't have added value to the model.
VotingPowerChange == 
  \E newValidators \in SUBSET Nodes:
    /\ newValidators /= {}
    /\ votingPowerRunning' \in [newValidators -> Nat]
    /\ \A v \in newValidators: votingPowerRunning'[v] > 0
    \* Note: votingPowerHasChanged' is set to true 
    \* even if votingPowerRunning' = votingPowerRunning
    /\ votingPowerHasChanged' = TRUE
    /\ UNCHANGED consumerVars
    /\ UNCHANGED << votingPowerHist, acks >>
    /\ lastAction' = "VotingPowerChange"

RcvPacket == 
  \E c \in activeConsumers:
    \* There must be a packet to be received
    /\ Len(ccvChannels[c]) /= 0
    /\ LET packet == Head(ccvChannels[c]) IN
      \* The voting power adjusts immediately, but the acknowledgement message 
      \* is sent later, on maturity 
      /\ votingPowerReferences' = [votingPowerReferences EXCEPT ![c] = packet]
      \* Maturity happens after MaturityDelay time has elapsed on c
      /\ maturityTimes' = [
        maturityTimes EXCEPT ![c] =
          ExtendFnBy(maturityTimes[c], packet, currentTimes[c] + MaturityDelay)
        ]
    \* Drop from channel, to unblock reception of other packets.
    /\ ccvChannels' = [ccvChannels EXCEPT ![c] = Tail(@)]
    /\ UNCHANGED providerVars
    /\ UNCHANGED currentTimes
    /\ UNCHANGED votingPowerHasChanged
    /\ lastAction' = "RcvPacket"

AckPacket == 
  \E c \in activeConsumers:
    \* Has been received
    \E packet \in DOMAIN maturityTimes[c]:
      \* Has matured 
      /\ currentTimes[c] >= maturityTimes[c][packet] 
      \* Hasn't been acknowledged
      /\ \A ack \in acks:
        \/ ack.chain /= c
        \/ ack.packetTime /= packet
      /\ acks' = acks \union { Ack(c, packet, currentTimes[c]) }
      /\ UNCHANGED consumerVars
      /\ UNCHANGED << votingPowerHist, votingPowerRunning >>
      /\ UNCHANGED votingPowerHasChanged
      /\ lastAction' = "AckPacket"

\* Partial action, always happens on Next
\* No need to purge data structures, we just don't access non-active indices
DropConsumers == 
  \E newActive \in SUBSET activeConsumers:
  /\ activeConsumers' = 
    { c \in newActive: ~PacketTimeoutForConsumer(c, ccvChannels'[c], currentTimes'[c], currentTimes'[ProviderChain], maturityTimes'[c]) }
  
      
\* Partial action, always happens on EndBlock, may also happen independently
AdvanceTimeCore ==
  \E newTimes \in [Chains -> Nat]:
    \* None regress
    \* Does not guarantee strict time progression in AdvanceTime.
    \* In EndProviderBlockAndSendPacket, provider time is forced 
    \* to strictly progress with an additional constraint.
    /\ \A c \in Chains: newTimes[c] >= currentTimes[c]
    /\ currentTimes' = newTimes

\* Time may also elapse without EndProviderBlockAndSendPacket.
AdvanceTime ==
  /\ AdvanceTimeCore
  /\ UNCHANGED providerVars
  /\ UNCHANGED << votingPowerReferences, ccvChannels, maturityTimes >>
  /\ UNCHANGED votingPowerHasChanged
  /\ lastAction' = "AdvanceTime"

EndProviderBlockAndSendPacket ==
  \* Packets are only sent if there is a VPC
  /\ votingPowerHasChanged
  /\ ccvChannels' = 
    [
      chain \in ConsumerChains |-> Append(
        ccvChannels[chain], 
        \* a packet is just the current time, the VP can be read from votingPowerHist
        currentTimes[ProviderChain]
        )
    ]
  \* Reset flag for next block
  /\ votingPowerHasChanged' = FALSE 
  /\ votingPowerHist' = ExtendFnBy(votingPowerHist, currentTimes[ProviderChain], votingPowerRunning)
  \* packet sending forces time progression on provider
  /\ AdvanceTimeCore
  /\ currentTimes'[ProviderChain] > currentTimes[ProviderChain]
  /\ UNCHANGED <<votingPowerReferences, maturityTimes>>
  /\ UNCHANGED <<votingPowerRunning, acks>>
  /\ lastAction' = "EndProviderBlockAndSendPacket"

\* If we ever drop all consumers, just do noting
Stagnate ==
  /\ UNCHANGED providerVars
  /\ UNCHANGED consumerVars
  /\ UNCHANGED activeConsumers
  /\ UNCHANGED bookkeepingVars
  /\ lastAction' = "Stagnate"

Next == 
  \//\ activeConsumers /= {}
    /\\/ EndProviderBlockAndSendPacket
      \/ VotingPowerChange
      \/ RcvPacket
      \/ AckPacket
      \/ AdvanceTime
    \* Drop timed out, maybe more
    /\ DropConsumers
    /\ boundedDrift' = 
      BoundedDeltas(currentTimes', activeConsumers' \union {ProviderChain}, MaxDrift)
  \//\ activeConsumers = {}
    /\ Stagnate

(*** PROPERTIES/INVARIANTS ***)

\* VCS must also mature on provider
LastVCSMatureOnProvider ==
  LastPacketTime + MaturityDelay <= currentTimes[ProviderChain]

VPCUpdateInProgress == 
  \* some chain has pending packets
  \/ \E c \in activeConsumers: 
    \/ Len(ccvChannels[c]) /= 0
    \/ \E packet \in DOMAIN maturityTimes[c]: maturityTimes[c][packet] < currentTimes[c]
  \* not enough time has elapsed on provider itself since last update
  \/ ~LastVCSMatureOnProvider

ActiveConsumersNotTimedOut ==
  \A c \in activeConsumers:
    ~PacketTimeoutForConsumer(c, ccvChannels[c], currentTimes[c], currentTimes[ProviderChain], maturityTimes[c])

\* Sanity- predicates check that the data structures don't take on unexpected values
SanityVP == 
  /\ \A t \in DOMAIN votingPowerHist:
    LET VP == votingPowerHist[t] IN
    VP /= UndefinedPower <=> 
      \A node \in DOMAIN VP: VP[node] >= 0
  /\ \A node \in DOMAIN votingPowerRunning: votingPowerRunning[node] >= 0

SanityRefs ==
  \A c \in ConsumerChains:
    votingPowerReferences[c] < 0 <=> votingPowerReferences[c] = UndefinedTime

SanityMaturity ==
  \A c \in ConsumerChains:
    \A t \in DOMAIN maturityTimes[c]:
      LET mt == maturityTimes[c][t] IN
      mt < 0 <=> mt = UndefinedTime
  
Sanity ==
  /\ SanityVP
  /\ SanityRefs
  /\ SanityMaturity


\* Since the clocks may drift, any delay that exceeds
\* Timeout + MaxDrift is perceived as timeout on all chains
AdjustedTimeout == Timeout + MaxDrift

\* Any packet sent by the provider is either received within Timeout, or
\* the consumer chain is no longer considered active.
RcvdInTime ==
  \A t \in DOMAIN votingPowerHist:
    \A c \in activeConsumers:
      \* If c is still active after Timeout has elapsed from packet t broadcast ...
      currentTimes[c] >= t + AdjustedTimeout =>
        \* ... then c must have received packet t
        t \in DOMAIN maturityTimes[c]

\* Any packet received by the consumer and matured is acknowledged 
\* within Timeout of reception, or the consumer is no longer considered active.
AckdInTime ==
  \A c \in activeConsumers:
    \A t \in DOMAIN maturityTimes[c]:
      \* If c is still active after Timeout has elapsed from packet t reception ...
      \* Note: Reception time = maturityTimes[c][p] - MaturityDelay
      currentTimes[ProviderChain] + MaturityDelay >= maturityTimes[c][t] + AdjustedTimeout =>
        \* ... then c must have acknowledged packet t
        \E ack \in acks:
          /\ ack.chain = c
          /\ ack.packetTime = t 


\* \* All packets are acked at the latest by Timeout, from all 
\* active consumers (or those consumers are removed from the active set)
\* It should be the case that RcvdInTime /\ AckdInTime => EventuallyAllAcks
EventuallyAllAcks == 
  \A t \in DOMAIN votingPowerHist:
    \* If a packet was sent at time t and enough time has elapsed, 
    \* s.t. all consumers should have responded ...
    currentTimes[ProviderChain] >= t + 2 * AdjustedTimeout =>
        \* then, all consumers have acked
        \A c \in activeConsumers:
          \E ack \in acks:
            /\ ack.chain = c
            /\ ack.packetTime = t

BoundedDrift ==
  \A c1, c2 \in activeConsumers \union {ProviderChain}:
    Delta(currentTimes[c1], currentTimes[c2]) <= MaxDrift

Inv ==
  \* /\ Sanity
  \* /\ ActiveConsumersNotTimedOut
  /\ (boundedDrift => 
      /\ RcvdInTime
      /\ AckdInTime
      )
  \* /\ RcvdInTime
  \* /\ AckdInTime
  


=============================================================================