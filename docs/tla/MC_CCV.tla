--------------------------- MODULE MC_CCV ---------------------------


Validators == {"1_OF_V", "2_OF_V", "3_OF_V"}
PowerInit == [v \in Validators |-> 10]
ConsumerChainsInit == {"1_OF_C", "2_OF_C"}
ConsumerChains == {"1_OF_C", "2_OF_C", "3_OF_C"}
MaturityDelay == 2
MaxHeight == 10

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

INSTANCE CCV

=============================================================================