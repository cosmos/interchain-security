--------------------------- MODULE CCV ---------------------------

EXTENDS Integers, Sequences, Apalache, typedefs

CONSTANT 
  \* @type: Set($node);
  Nodes,
  \* @type: Set($node);
  NodesInit,
  \* @type: $Int;
  PowerInit, 
  \* @type: Set($chain);
  ConsumerChains,
  \* @type: Set($chain);
  ConsumerChainsInit, 
  \* @type: $height;
  MaturityDelay,
  \* @type: $height;
  MaxHeight,
  \* @type: $height;
  Timeout

Heights == 0 .. MaxHeight
UndefinedHeight == -1

\* Provider chain ID, assumed to be distinct from all consumer chain IDs
ProviderChain == "provider_OF_C"

UndefinedPower == [node \in Nodes |-> -1]

Chains == ConsumerChains \union {ProviderChain}

VARIABLES
  \* @type: $height -> $votingPowerOnChain;
  votingPowerHist,
  \* @type: $votingPowerOnChain;
  votingPowerRunning,
  \* @type: Set($chain);
  activeConsumers,
  \* @type: $chain -> $height;
  heights,
  \* @type: $chain -> $height;
  votingPowerReferences,
  \* @type: $chain -> Seq($packet);
  ccvChannels,
  \* @type: Set($ack);
  acks,
  \* @type: Str;
  lastAction,
  \* @type: $height;
  lastPacketAt

vars == <<
  votingPowerHist, votingPowerRunning, activeConsumers,
  heights, votingPowerReferences, ccvChannels, acks, lastPacketAt
        >>

Init == 
  /\ votingPowerHist = [h \in Heights |-> UndefinedPower]
  /\ votingPowerRunning = [node \in NodesInit |-> PowerInit]
  /\ activeConsumers = ConsumerChainsInit
  /\ heights = [chain \in Chains |-> 0]
  /\ votingPowerReferences = [chain \in ConsumerChains |-> UndefinedHeight]
  /\ ccvChannels = [chain \in ConsumerChains |-> <<>>]
  /\ acks = {}
  /\ lastPacketAt = -1
  /\ lastAction = "Init"

\* @type: ($chain, $height, $height) => $ack;
Ack(c, packetH, maturityH) == 
  [chain |-> c, packetProviderHeight |-> packetH, maturityConsumerHeight |-> maturityH]

VotingPowerChange == 
  \E newValidators \in SUBSET DOMAIN votingPowerRunning:
    /\ votingPowerRunning' \in [newValidators -> Nat]
    /\ UNCHANGED << votingPowerHist, activeConsumers, heights, votingPowerReferences, ccvChannels, acks, lastPacketAt >>
    /\ lastAction' = "VotingPowerChange"

Undelegate == 
  \E v \in DOMAIN votingPowerRunning:
    /\ votingPowerRunning[v] > 0
    /\ \E reduction \in Int:
      /\ 0 < reduction 
      /\ reduction <= votingPowerRunning[v]
      /\ votingPowerRunning' = [votingPowerRunning EXCEPT ![v] = @ - reduction]
    /\ UNCHANGED << votingPowerHist, activeConsumers, heights, votingPowerReferences, ccvChannels, acks, lastPacketAt >>
    /\ lastAction' = "Undelegate"

Redelegate == 
  \E src, dest \in DOMAIN votingPowerRunning:
    /\ src /= dest
    /\ votingPowerRunning[src] > 0
    /\ \E delta \in Int:
      /\ 0 < delta 
      /\ delta <= votingPowerRunning[src]
      /\ votingPowerRunning' = [votingPowerRunning EXCEPT 
        ![src] = @ - delta,
        ![dest] = @ + delta
        ]
    /\ UNCHANGED << votingPowerHist, activeConsumers, heights, votingPowerReferences, ccvChannels, acks, lastPacketAt >>
    /\ lastAction' = "Redelegate"

\* TODO: if slow, merge unbond/undelegate/redelegate actions into one
Unbond == 
  LET currentValidators == DOMAIN votingPowerRunning IN
  \E v \in currentValidators:
    /\ votingPowerRunning' = 
      [ validator \in currentValidators \ {v} |-> votingPowerRunning[v] ]
    /\ UNCHANGED << votingPowerHist, activeConsumers, heights, votingPowerReferences, ccvChannels, acks, lastPacketAt >>
    /\ lastAction' = "Unbond"

AckPacket == 
  \E c \in activeConsumers:
    /\ ccvChannels[c] /= <<>>
    /\ LET packet == Head(ccvChannels[c]) IN
      /\ votingPowerReferences' = [votingPowerReferences EXCEPT ![c] = packet]
      \* The voting power decreases immediately, but the ack message contains
      \* the height at which the VSC will mature 
      /\ acks' = acks \union { Ack(c, packet, heights[c] + MaturityDelay) }
      /\ ccvChannels' = [ccvChannels EXCEPT ![c] = Tail(@)]
    /\ heights' = [heights EXCEPT ![c] = @ + MaturityDelay]
    /\ UNCHANGED << votingPowerHist, votingPowerRunning, activeConsumers, lastPacketAt>>
    /\ lastAction' = "AckPacket"

AdvanceConsumerHeight ==
  \E c \in ConsumerChains:
    \E h \in Int:
      /\ h > heights[c]
      /\ h < MaxHeight
      /\ heights' = [heights EXCEPT ![c] = h]
      /\ UNCHANGED <<votingPowerHist, votingPowerRunning, activeConsumers,votingPowerReferences, ccvChannels, acks, lastPacketAt>>
      /\ lastAction' = "AdvanceConsumerHeight"

AddNewConsumer ==
  \E c \in ConsumerChains:
    /\ c \notin activeConsumers
    /\ activeConsumers' = activeConsumers \union {c}
    /\ heights' = [heights EXCEPT ![c] = 0]
    /\ votingPowerReferences' = [votingPowerReferences EXCEPT ![c] = UndefinedHeight]
    /\ ccvChannels' = 
      [ ccvChannels EXCEPT ![c] = 
        <<heights[ProviderChain]>>
      ]
    /\ acks' = { ack \in acks: ack.chain /= c }
    /\ lastAction' = "AddNewConsumer"
    /\ UNCHANGED << votingPowerHist, votingPowerRunning,  lastPacketAt >>

DropConsumers == 
  \E newActive \in SUBSET activeConsumers:
  /\ newActive /= activeConsumers
  /\ activeConsumers' = newActive
  \* No need to purge data structures, we just don't access non-active indices
  /\ lastAction' = "DropConsumers"
  /\ UNCHANGED <<votingPowerHist, votingPowerRunning, heights, votingPowerReferences, ccvChannels, acks, lastPacketAt>>
      
PacketTimeoutForConsumer(c, cutoff) == 
  /\ ccvChannels[c] /= <<>>
  \* Head is always the oldest packet, so if there is a timeout for some packet, 
  \* there must be one for Head too
  /\ cutoff > Head(ccvChannels[c]) + Timeout
    

DropTimedOutConsumers ==
  /\ activeConsumers' = { c \in activeConsumers: ~PacketTimeoutForConsumer(c, heights[ProviderChain]) }
  /\ lastAction' = "DropTimedOutConsumers"
  /\ UNCHANGED <<votingPowerHist, votingPowerRunning, heights, votingPowerReferences, ccvChannels, acks, lastPacketAt>>

EndProviderBlockAndSendPacket ==
  LET providerH == heights[ProviderChain] IN
  /\ IF lastPacketAt /= -1 /\ votingPowerHist[lastPacketAt] /= votingPowerRunning
     THEN 
      /\ ccvChannels' = 
        [
          chain \in ConsumerChains |-> Append(
            ccvChannels[chain], 
            \* a packet is just the current provider height, the VP can be read from votingPowerHist
            heights[ProviderChain] 
            )
        ]
      /\ lastPacketAt' = providerH 
      /\ votingPowerHist' = [votingPowerHist EXCEPT ![providerH] = votingPowerRunning]
      ELSE UNCHANGED <<ccvChannels, lastPacketAt, votingPowerHist>>
  /\ \E h \in Int:
    /\ h > providerH
    /\ h < MaxHeight
    /\ heights' = [heights EXCEPT ![ProviderChain] = h]
    \* Cut all customers now considered inactive by timeout
    /\ activeConsumers' = 
      { c \in activeConsumers: ~PacketTimeoutForConsumer(c, h) }
  /\ UNCHANGED <<votingPowerRunning, votingPowerReferences, acks>>
  /\ lastAction' = "EndProviderBlockAndSendPacket"

Next == 
    \/ EndProviderBlockAndSendPacket
    \* \/ Undelegate
    \* \/ Redelegate
    \* \/ Unbond
    \/ VotingPowerChange
    \/ AckPacket
    \/ AdvanceConsumerHeight
    \/ AddNewConsumer
    \/ DropConsumers


LastVCSMatureOnProvider ==
  lastPacketAt + MaturityDelay <= heights[ProviderChain]

VPCUpdateInProgress == 
  \* some chain has pending packets
  \/ \E c \in activeConsumers: ccvChannels[c] /= <<>>
  \* not enough time has elapsed on provider itself since last update
  \/ ~LastVCSMatureOnProvider
  \* All chains have processed a packet, but not enough time has elapsed
  \/ \E ack \in acks: heights[ack.chain] < ack.maturityHeight
  
\* AgreementOnPower == 
\*   \A c \in activeConsumers:
\*     votingPower[c] = votingPowerOnProviderLastBlock


ActiveConsumersNotTimedOut ==
  \A c \in activeConsumers:
    ~PacketTimeoutForConsumer(c, heights[ProviderChain])

SanityVP == 
  /\ \A h \in Heights:
    LET VP == votingPowerHist[h] IN
    VP /= UndefinedPower <=> 
      \A node \in DOMAIN VP: VP[node] >= 0
  /\ \A node \in DOMAIN votingPowerRunning: votingPowerRunning[node] >= 0

SanityHeight ==
  \A c \in Chains:
    heights[c] >= 0

SanityRefs ==
  \A c \in ConsumerChains:
    votingPowerReferences[c] < 0 <=> votingPowerReferences[c] = UndefinedHeight
  
Sanity ==
  /\ SanityVP
  /\ SanityHeight
  /\ SanityRefs

\* All packets are acked at the latest by Timeout, from all 
\* active consumers (or those consumers are removed from the active set)
EventuallyAllAcks == 
  \A h \in Heights:
    \* If a packet was sent at height h and enough time has elapsed, where all consumers should have 
      \* responded ...
    (votingPowerHist[h] /= UndefinedPower /\ heights[ProviderChain] >= h + Timeout) =>
        \* then, all consumers have acked
        \* TODO: change chain height to real-time, and check all have _matured_ too
        \A c \in activeConsumers:
          \E ack \in acks:
            /\ ack.chain = c
            /\ ack.packetProviderHeight = h
      

Inv == TRUE
  \* /\ Sanity
  \* /\ ActiveConsumersNotTimedOut
  /\ EventuallyAllAcks


=============================================================================