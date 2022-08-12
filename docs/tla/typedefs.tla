--------------------------- MODULE typedefs ---------------------------
(* 
  @typeAlias: chain = C; chain type
  @typeAlias: validator = V; validator type
  @typeAlias: power = Int; voting power
  @typeAlias: height = Int; chain height
  @typeAlias: id = Int; request ID
  @typeAlias: votingPowerOnChain = $validator -> $power;
  @typeAlias: packet = $votingPowerOnChain;
  @typeAlias: votingPower = $chain -> $votingPowerOnChain;
  @typeAlias: undelegation = { validator: $validator, height: $height, powerReduction: $power, id: $id };
  @typeAlias: ack = { chain: $chain, id: $id, maturityHeight: $height };
  @typeAlias: redelegation = { src: $validator, dest: $validator, height: $height, powerDelta: $power, id: $id };
  @typeAlias: unbond = { validator: $validator, height: $height, id: $id };
  @typeAlias: message = 
      UndelegateInit($undelegation) 
    | UndelegateAck($ack)
    | RedelegateInit($redelegation) 
    | RedelegateAck($ack)
    | UnbondInit($unbond) 
    | UnbondAck($ack);
*)
AliasesCVV == TRUE
=============================================================================