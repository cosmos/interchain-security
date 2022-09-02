--------------------------- MODULE MC_CCV ---------------------------

EXTENDS Integers

Nodes == {"1_OF_N", "2_OF_N", "3_OF_N", "4_OF_N"}
ConsumerChains == {"1_OF_C", "2_OF_C", "3_OF_C", "4_OF_C"}
\* MaturityDelay == 3 * 7 * 24 \* h
\* Timeout == 4 * 7 * 24 \* h
\* MaxDrift == 24 \* h

CONSTANT 
  \* @type: $time;
  MaturityDelay,
  \* @type: $time;
  Timeout,
  \* @type: $time;
  MaxDrift

CInit ==
  /\ MaturityDelay \in Nat
  /\ Timeout \in Nat
  /\ MaxDrift \in Nat
  /\ MaxDrift < Timeout

\* Provider chain only
VARIABLES
  \* @type: $time -> $votingPowerOnChain;
  votingPowerHist,
  \* @type: $votingPowerOnChain;
  votingPowerRunning,
  \* @type: Set($chain);
  activeConsumers,
  \* @type: Set($ack);
  acks

\* Consumer chains or both
VARIABLES  
  \* @type: $chain -> $time;
  votingPowerReferences,
  \* @type: $chain -> Seq($packet);
  ccvChannelsPending,
  \* @type: $chain -> Seq($packet);
  ccvChannelsResolved,
  \* @type: $chain -> $time;
  currentTimes,
  \* @type: $chain -> $time -> $time;
  maturityTimes

\* Bookkeeping
VARIABLES 
  \* @type: Str;
  lastAction,
  \* @type: Bool;
  votingPowerHasChanged,
  \* @type: Bool;
  boundedDrift

INSTANCE CCV

=============================================================================