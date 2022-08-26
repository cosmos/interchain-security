--------------------------- MODULE MC_CCV ---------------------------


Nodes == {"1_OF_N", "2_OF_N", "3_OF_N", "4_OF_N"}
ConsumerChains == {"1_OF_C", "2_OF_C", "3_OF_C", "4_OF_C"}
MaturityDelay == 2
Timeout == 4

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
  ccvChannels,
  \* @type: $chain -> $time;
  currentTimes,
  \* @type: $chain -> $time -> $time;
  maturityTimes

\* Bookkeeping
VARIABLES 
  \* @type: Str;
  lastAction,
  \* @type: Bool;
  votingPowerHasChanged

INSTANCE CCV

=============================================================================