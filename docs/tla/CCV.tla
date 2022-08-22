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
  \* @type: $time;
  MaturityDelay,
  \* @type: $time;
  MaxTime,
  \* @type: $time;
  Timeout

ASSUME (Timeout > MaturityDelay)

Times == 0 .. MaxTime
UndefinedTime == -1

\* Provider chain ID, assumed to be distinct from all consumer chain IDs
ProviderChain == "provider_OF_C"

UndefinedPower == [node \in Nodes |-> -1]

Chains == ConsumerChains \union {ProviderChain}

VARIABLES
  \* @type: $time -> $votingPowerOnChain;
  votingPowerHist,
  \* @type: $votingPowerOnChain;
  votingPowerRunning,
  \* @type: Set($chain);
  activeConsumers,
  \* @type: $chain -> $time;
  votingPowerReferences,
  \* @type: $chain -> Seq($packet);
  ccvChannels,
  \* @type: Set($ack);
  acks,
  \* @type: Str;
  lastAction,
  \* @type: $time;
  lastPacketAt,
  \* @type: $time;
  currentTime,
  \* @type: $chain -> $time -> $time;
  maturityTimes

vars == <<
  votingPowerHist, votingPowerRunning, activeConsumers,
  votingPowerReferences, ccvChannels, acks, lastPacketAt
        >>

Init == 
  /\ votingPowerHist = [h \in Times |-> UndefinedPower]
  /\ votingPowerRunning = [node \in NodesInit |-> PowerInit]
  /\ activeConsumers = ConsumerChainsInit
  /\ votingPowerReferences = [chain \in ConsumerChains |-> UndefinedTime]
  /\ ccvChannels = [chain \in ConsumerChains |-> <<>>]
  /\ acks = {}
  /\ lastPacketAt = UndefinedTime
  /\ currentTime = 0
  /\ maturityTimes = [c \in ConsumerChains |-> [t \in Times |-> UndefinedTime]]
  /\ lastAction = "Init"

\* @type: ($chain, $time, $time) => $ack;
Ack(c, packetT, ackT) == 
  [chain |-> c, packetTime |-> packetT, ackTime |-> ackT]

VotingPowerChange == 
  \E newValidators \in SUBSET Nodes:
    /\ newValidators /= {}
    /\ votingPowerRunning' \in [newValidators -> Nat]
    /\ \A v \in newValidators: votingPowerRunning'[v] > 0
    /\ UNCHANGED << votingPowerHist, activeConsumers, votingPowerReferences, ccvChannels, acks, lastPacketAt, currentTime, maturityTimes>>
    /\ lastAction' = "VotingPowerChange"

\* Undelegate == 
\*   \E v \in DOMAIN votingPowerRunning:
\*     /\ votingPowerRunning[v] > 0
\*     /\ \E reduction \in Int:
\*       /\ 0 < reduction 
\*       /\ reduction <= votingPowerRunning[v]
\*       /\ votingPowerRunning' = [votingPowerRunning EXCEPT ![v] = @ - reduction]
\*     /\ UNCHANGED << votingPowerHist, activeConsumers, votingPowerReferences, ccvChannels, acks, lastPacketAt >>
\*     /\ lastAction' = "Undelegate"

\* Redelegate == 
\*   \E src, dest \in DOMAIN votingPowerRunning:
\*     /\ src /= dest
\*     /\ votingPowerRunning[src] > 0
\*     /\ \E delta \in Int:
\*       /\ 0 < delta 
\*       /\ delta <= votingPowerRunning[src]
\*       /\ votingPowerRunning' = [votingPowerRunning EXCEPT 
\*         ![src] = @ - delta,
\*         ![dest] = @ + delta
\*         ]
\*     /\ UNCHANGED << votingPowerHist, activeConsumers, votingPowerReferences, ccvChannels, acks, lastPacketAt >>
\*     /\ lastAction' = "Redelegate"

\* Unbond == 
\*   LET currentValidators == DOMAIN votingPowerRunning IN
\*   \E v \in currentValidators:
\*     /\ votingPowerRunning' = 
\*       [ validator \in currentValidators \ {v} |-> votingPowerRunning[v] ]
\*     /\ UNCHANGED << votingPowerHist, activeConsumers, votingPowerReferences, ccvChannels, acks, lastPacketAt >>
\*     /\ lastAction' = "Unbond"

RcvPacket == 
  \E c \in activeConsumers:
    /\ Len(ccvChannels[c]) /= 0
    /\ LET packet == Head(ccvChannels[c]) IN
      \* The voting power adjusts immediately, but the ack message 
      \* is sent on maturity 
      /\ votingPowerReferences' = [votingPowerReferences EXCEPT ![c] = packet]
      /\ maturityTimes' = [maturityTimes EXCEPT ![c][packet] = currentTime + MaturityDelay]
    /\ UNCHANGED <<ccvChannels, acks>>
    /\ UNCHANGED << votingPowerHist, votingPowerRunning, activeConsumers, lastPacketAt, currentTime>>
    /\ lastAction' = "RcvPacket"

AckPacket == 
  \E c \in activeConsumers:
    /\ Len(ccvChannels[c]) /= 0
    /\ LET packet == Head(ccvChannels[c]) IN
      \* packet is received iff maturityTimes is defined
      /\ maturityTimes[c][packet] /= UndefinedTime 
      /\ currentTime >= maturityTimes[c][packet]  
      /\ acks' = acks \union { Ack(c, packet, currentTime) }
      /\ ccvChannels' = [ccvChannels EXCEPT ![c] = Tail(@)]
    /\ UNCHANGED votingPowerReferences
    /\ UNCHANGED << votingPowerHist, votingPowerRunning, activeConsumers, lastPacketAt, currentTime, maturityTimes>>
    /\ lastAction' = "AckPacket"

AdvanceTime ==
  \E t \in Int:
    /\ t > currentTime
    /\ t <= MaxTime
    /\ currentTime' = t
    /\ UNCHANGED <<votingPowerHist, votingPowerRunning, activeConsumers,votingPowerReferences, ccvChannels, acks, lastPacketAt, maturityTimes>>
    /\ lastAction' = "AdvanceTime"

AddNewConsumer ==
  \E c \in ConsumerChains:
    /\ c \notin activeConsumers
    /\ activeConsumers' = activeConsumers \union {c}
    /\ votingPowerReferences' = [votingPowerReferences EXCEPT ![c] = UndefinedTime]
    /\ ccvChannels' = 
      \* Channel empty
      [ ccvChannels EXCEPT ![c] = <<>>]
    /\ maturityTimes' = [maturityTimes EXCEPT ![c] = [t \in Times |-> UndefinedTime]]
    /\ acks' = { ack \in acks: ack.chain /= c }
    /\ lastAction' = "AddNewConsumer"
    /\ UNCHANGED << votingPowerHist, votingPowerRunning,  lastPacketAt, currentTime >>

DropConsumers == 
  \E newActive \in SUBSET activeConsumers:
  /\ newActive /= activeConsumers
  /\ activeConsumers' = newActive
  \* No need to purge data structures, we just don't access non-active indices
  /\ lastAction' = "DropConsumers"
  /\ UNCHANGED <<votingPowerHist, votingPowerRunning,  votingPowerReferences, ccvChannels, acks, lastPacketAt, currentTime, maturityTimes>>
      
PacketTimeoutForConsumer(c, t) == 
  /\ Len(ccvChannels[c]) /= 0
  \* Head is always the oldest packet, so if there is a timeout for some packet, 
  \* there must be one for Head too
  /\ t > Head(ccvChannels[c]) + Timeout
    

DropTimedOutConsumers ==
  /\ activeConsumers' = { c \in activeConsumers: ~PacketTimeoutForConsumer(c, currentTime) }
  /\ lastAction' = "DropTimedOutConsumers"
  /\ UNCHANGED <<votingPowerHist, votingPowerRunning, votingPowerReferences, ccvChannels, acks, lastPacketAt, currentTime, maturityTimes>>

EndProviderBlockAndSendPacket ==
  /\ IF lastPacketAt /= -1 /\ votingPowerHist[lastPacketAt] /= votingPowerRunning
     THEN 
      /\ ccvChannels' = 
        [
          chain \in ConsumerChains |-> Append(
            ccvChannels[chain], 
            \* a packet is just the current time, the VP can be read from votingPowerHist
            currentTime 
            )
        ]
      /\ lastPacketAt' = currentTime 
      /\ votingPowerHist' = [votingPowerHist EXCEPT ![currentTime] = votingPowerRunning]
      ELSE UNCHANGED <<ccvChannels, lastPacketAt, votingPowerHist>>
  \* packet sending forces time progression
  /\ \E t \in Int:
    /\ t > currentTime
    /\ t <= MaxTime
    /\ currentTime' = t
    \* Cut all customers now considered inactive by timeout
    /\ activeConsumers' = 
      { c \in activeConsumers: ~PacketTimeoutForConsumer(c, t) }
  /\ UNCHANGED <<votingPowerRunning, votingPowerReferences, acks, maturityTimes>>
  /\ lastAction' = "EndProviderBlockAndSendPacket"

Next == 
    \/ EndProviderBlockAndSendPacket
    \* \/ Undelegate
    \* \/ Redelegate
    \* \/ Unbond
    \/ VotingPowerChange
    \/ RcvPacket
    \/ AckPacket
    \/ AdvanceTime
    \/ AddNewConsumer
    \/ DropConsumers


LastVCSMatureOnProvider ==
  lastPacketAt + MaturityDelay <= currentTime

VPCUpdateInProgress == 
  \* some chain has pending packets
  \/ \E c \in activeConsumers: ccvChannels[c] /= <<>>
  \* not enough time has elapsed on provider itself since last update
  \/ ~LastVCSMatureOnProvider
  
\* AgreementOnPower == 
\*   \A c \in activeConsumers:
\*     votingPower[c] = votingPowerOnProviderLastBlock


ActiveConsumersNotTimedOut ==
  \A c \in activeConsumers:
    ~PacketTimeoutForConsumer(c, currentTime)

SanityVP == 
  /\ \A t \in Times:
    LET VP == votingPowerHist[t] IN
    VP /= UndefinedPower <=> 
      \A node \in DOMAIN VP: VP[node] >= 0
  /\ \A node \in DOMAIN votingPowerRunning: votingPowerRunning[node] >= 0

SanityRefs ==
  \A c \in ConsumerChains:
    votingPowerReferences[c] < 0 <=> votingPowerReferences[c] = UndefinedTime

SanityMaturity ==
  \A c \in ConsumerChains:
    \A t \in Times:
      maturityTimes[c][t] < 0 <=> maturityTimes[c][t] = UndefinedTime
  
Sanity ==
  /\ SanityVP
  /\ SanityRefs
  /\ SanityMaturity

\* @type: ($time) => Bool;
PacketSentAtTime(t) == votingPowerHist[t] /= UndefinedPower

\* All packets are acked at the latest by Timeout, from all 
\* active consumers (or those consumers are removed from the active set)
EventuallyAllAcks == 
  \A t \in Times:
    \* If a packet was sent at time t and enough time has elapsed, 
    \* s.t. all consumers should have responded ...
    (PacketSentAtTime(t) /\ currentTime >= t + Timeout) =>
        \* then, all consumers have acked
        \A c \in activeConsumers:
          \E ack \in acks:
            /\ ack.chain = c
            /\ ack.packetTime = t
      

Inv ==
  /\ Sanity
  /\ ActiveConsumersNotTimedOut
  /\ EventuallyAllAcks
  


=============================================================================