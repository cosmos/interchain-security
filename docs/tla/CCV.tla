--------------------------- MODULE CCV ---------------------------

EXTENDS Integers, Sequences, Apalache, typedefs

CONSTANT 
  \* @type: Set($validator);
  Validators,
  \* @type: $validator -> $power;
  PowerInit, \* assume DOMAIN PowerInit == Validators
  \* @type: Set($chain);
  ConsumerChainsInit, 
  \* @type: Set($chain);
  ConsumerChains, 
  \* @type: $height;
  MaturityDelay,
  \* @type: $height;
  MaxHeight

Heights == 0 .. MaxHeight

\* Provider chain ID, assumed to be distinct from all consumer chain IDs
ProviderChain == "provider_OF_C"

Chains == ConsumerChains \union {ProviderChain}

(* 
Consumer chain variables:
  votingPowerAtHeight - for each trio of (C, H, V), defines the voting
  power of validator V on chain C at height H.
  "removed" validators are modeled as having power 0.
  Due to communication delays, votingPowerAtHeight[c,h,v], for a given 
  consumer chain c, may differ from votingPowerAtHeight[provider, h v], 
  but must be equal to votingPowerAtHeight[provider, hh, v] for some hh < h.

  messages - a history of sent messages. Channels are implicitly encoded
  in the message format.
*)
VARIABLES
  \* @type: $votingPower;
  votingPower,
  \* @type: $votingPowerOnChain;
  votingPowerOnProviderLastBlock,
  \* @type: Set($chain);
  activeConsumers,
  \* @type: $chain -> $height;
  heights,
  \* @type: $chain -> Seq($packet);
  ccvChannels,
  \* @type: Set($ack);
  acks,
  \* @type: $height;
  lastPacketAt,
  \* @type: Str;
  lastAction

vars == <<
  votingPower, votingPowerOnProviderLastBlock, activeConsumers,
  heights, ccvChannels, acks, lastPacketAt, lastAction
        >>

Init == 
  /\ votingPower = [chain \in Chains |-> PowerInit]
  /\ votingPowerOnProviderLastBlock = PowerInit 
  /\ activeConsumers = ConsumerChainsInit
  /\ heights = [chain \in Chains |-> 0]
  /\ ccvChannels = [chain \in ConsumerChains |-> <<>>]
  /\ acks = {}
  /\ lastPacketAt = 0
  /\ lastAction = "Init"

\* @type: ($chain, $id, $height) => $ack;
Ack(c, id, h) == [chain |-> c, id |-> id, maturityHeight |-> h]
\* @type: ($votingPowerOnChain, $height) => $packet;
Packet(vp, h) == [newVP |-> vp, providerHeight |-> h]

EndProviderBlockAndSendPacket ==
  /\ IF votingPower[ProviderChain] /= votingPowerOnProviderLastBlock
     THEN 
     /\ ccvChannels' = 
      [
        chain \in ConsumerChains |-> Append(
          ccvChannels[chain], 
          Packet(votingPower[ProviderChain], heights[ProviderChain])
          )
      ]
     /\ lastPacketAt' = heights[ProviderChain]
     ELSE
     /\ UNCHANGED <<ccvChannels, lastPacketAt>>
  /\ \E h \in Int:
    /\ h > heights[ProviderChain]
    /\ h < MaxHeight
    /\ heights' = [heights EXCEPT ![ProviderChain] = h]
  /\ votingPowerOnProviderLastBlock' = votingPower[ProviderChain]
  /\ UNCHANGED <<votingPower, activeConsumers, acks>>  
  /\ lastAction' = "EndProviderBlockAndSendPacket"

Undelegate == 
  \E v \in Validators:
    /\ votingPower[ProviderChain][v] > 0 \* Only active validators can undelegate
    /\ \E reduction \in Int:
      /\ 0 < reduction 
      /\ reduction < votingPower[ProviderChain][v] \* strictly <, otherwise unbond
      /\ votingPower' = [votingPower EXCEPT ![ProviderChain][v] = @ - reduction]
    /\ UNCHANGED <<votingPowerOnProviderLastBlock, activeConsumers, heights, ccvChannels, acks, lastPacketAt>>
    /\ lastAction' = "Undelegate"

Redelegate == 
  \E src, dest \in Validators:
    /\ src /= dest
    /\ votingPower[ProviderChain][src] > 0 \* Only active validators can redelegate
    /\ \E delta \in Int:
      /\ 0 < delta 
      /\ delta < votingPower[ProviderChain][src] \* strictly <, otherwise unbond
      /\ votingPower' = [votingPower EXCEPT 
        ![ProviderChain][src] = @ - delta,
        ![ProviderChain][dest] = @ + delta
        ]
    /\ UNCHANGED <<votingPowerOnProviderLastBlock, activeConsumers, heights, ccvChannels, acks, lastPacketAt>>
    /\ lastAction' = "Redelegate"

\* TODO: if slow, merge unbond/undelegate/redelegate actions into one
Unbond == 
  \E v \in Validators:
    /\ votingPower[ProviderChain][v] > 0 \* Only active validators can unbond
    /\ votingPower' = [votingPower EXCEPT ![ProviderChain][v] = 0]
    /\ UNCHANGED <<votingPowerOnProviderLastBlock, activeConsumers, heights, ccvChannels, acks, lastPacketAt>>
    /\ lastAction' = "Unbond"

AckPacket == 
  \E c \in activeConsumers:
    /\ ccvChannels[c] /= <<>>
    /\ LET packet == Head(ccvChannels[c]) IN
      /\ \A ack \in acks:
        \/ ack.chain /= c
        \/ ack.id /= packet.id
      /\ votingPower' = [votingPower EXCEPT ![c] = packet.newVP]
      \* The voting power decreases immediately, but the ack message contains
      \* the height at which the VSC will mature 
      /\ acks' = acks \union { Ack(c, packet.id, heights[c] + MaturityDelay) }
      /\ ccvChannels' = [ccvChannels EXCEPT ![c] = Tail(@)]
    /\ UNCHANGED <<votingPowerOnProviderLastBlock, activeConsumers, heights, lastPacketAt>>
    /\ lastAction' = "AckPacket"

AdvanceConsumerHeight ==
  \E c \in ConsumerChains:
    \E h \in Int:
      /\ h > heights[c]
      /\ h < MaxHeight
      /\ heights' = [heights EXCEPT ![c] = h]
      /\ UNCHANGED <<votingPowerOnProviderLastBlock, activeConsumers, acks, votingPower, ccvChannels, lastPacketAt>>
      /\ lastAction' = "AdvanceConsumerHeight"

AddNewConsumer ==
  \E c \in ConsumerChains:
    /\ c \notin activeConsumers
    /\ activeConsumers' = activeConsumers \union {c}
    /\ ccvChannels' = 
      [ ccvChannels EXCEPT ![c] = 
        <<Packet(votingPower[ProviderChain], heights[ProviderChain])>>
      ]
    /\ lastAction' = "AddNewConsumer"
    /\ UNCHANGED 
      << votingPower, votingPowerOnProviderLastBlock, (*activeConsumers,*)
         heights, (*ccvChannels,*) acks, lastPacketAt(*, lastAction*) >>

\* @type: ($chain) => Bool;
DropConsumer(c) == 
  /\ c \in activeConsumers
  /\ activeConsumers' = activeConsumers \ {c}
  /\ ccvChannels' = [ ccvChannels EXCEPT ![c] = <<>> ]
  /\ lastAction' = "AddNewConsumer"
  /\ UNCHANGED 
      << votingPower, votingPowerOnProviderLastBlock, (*activeConsumers,*)
         heights, (*ccvChannels,*) acks, lastPacketAt(*, lastAction*) >>
      

Next == 
  \/ EndProviderBlockAndSendPacket
  \/ Undelegate
  \/ Redelegate
  \/ Unbond
  \/ AckPacket
  \/ AdvanceConsumerHeight
  \* \/ AddNewConsumer
  \* \/ \E c \in activeConsumers: DropConsumer(c)


LastVCSMatureOnProvider ==
  lastPacketAt + MaturityDelay <= heights[ProviderChain]

VPCUpdateInProgress == 
  \* some chain has pending packets
  \/ \E c \in activeConsumers: ccvChannels[c] /= <<>>
  \* not enough time has elapsed on provider itself since last update
  \/ ~LastVCSMatureOnProvider
  \* All chains have processed a packet, but not enough time has elapsed
  \/ \E ack \in acks: heights[ack.chain] < ack.maturityHeight
  
AgreementOnPower == 
  \A c \in activeConsumers:
    votingPower[c] = votingPowerOnProviderLastBlock

Inv == 
  ~VPCUpdateInProgress => AgreementOnPower


=============================================================================