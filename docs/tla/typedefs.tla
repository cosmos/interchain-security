--------------------------- MODULE typedefs ---------------------------
(* 
  @typeAlias: chain = C; chain type
  @typeAlias: node = N; node type
  @typeAlias: power = Int; voting power
  @typeAlias: height = Int; chain height
  @typeAlias: time = Int; 
  @typeAlias: votingPowerOnChain = $node -> $power;
  @typeAlias: packet = $height;
  @typeAlias: ack = [chain: $chain, packetProviderHeight: $height, maturityConsumerHeight: $height];
*)
AliasesCVV == TRUE
=============================================================================