--------------------------- MODULE MC_CCV ---------------------------


Validators == {"1_OF_V", "2_OF_V", "3_OF_V"}
PowerInit == [v \in Validators |-> 10]
ConsumerChainsInit == {"1_OF_C", "2_OF_C"}
AllConsumerChains == {"1_OF_C", "2_OF_C", "3_OF_C"}
MaturityDelay == 2
MaxHeight == 10

VARIABLES
  \* @type: $votingPower;
  votingPower,
  \* @type: Set($message);
  messages,
  \* @type: Set($chain);
  activeConsumers,
  \* @type: $chain -> $height;
  heights,
  \* @type: $id;
  nextId

INSTANCE CCV

=============================================================================