--------------------------- MODULE typedefs ---------------------------
(* 
  @typeAlias: chain = C; chain type
  @typeAlias: node = N; node type
  @typeAlias: power = Int; voting power
  @typeAlias: time = Int; 
  @typeAlias: votingPowerOnChain = $node -> $power;
  @typeAlias: packet = $time;
  @typeAlias: ack = [chain: $chain, packetTime: $time, ackTime: $time];
*)
AliasesCVV == TRUE
=============================================================================