--------------------------- MODULE MC_CCV ---------------------------


Nodes == {"1_OF_N", "2_OF_N", "3_OF_N", "4_OF_N"}
NodesInit == {"1_OF_N", "2_OF_N"}
PowerInit == 10
ConsumerChainsInit == {"1_OF_C", "2_OF_C"}
ConsumerChains == {"1_OF_C", "2_OF_C", "3_OF_C", "4_OF_C"}
MaturityDelay == 2
Timeout == 4
MaxTime == 100

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

INSTANCE CCV

=============================================================================