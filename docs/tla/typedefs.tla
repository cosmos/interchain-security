--------------------------- MODULE typedefs ---------------------------
(* 
  @typeAlias: chain = C; chain type
  @typeAlias: validator = V; validator type
  @typeAlias: power = Int; voting power
  @typeAlias: height = Int; chain height
  @typeAlias: id = Int; request ID
  @typeAlias: votingPowerOnChain = $validator -> $power;
  @typeAlias: votingPower = $chain -> $votingPowerOnChain;
  @typeAlias: packet = [newVP: $votingPowerOnChain, providerHeight: $height];
  @typeAlias: ack = [chain: $chain, id: $id, maturityHeight: $height];
*)
AliasesCVV == TRUE
=============================================================================