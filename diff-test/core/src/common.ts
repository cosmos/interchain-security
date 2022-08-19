type Chain = 'provider' | 'consumer';

type Validator = number;

interface Action {
  kind: string;
}

type Delegate = {
  kind: string;
  val: Validator;
  amt: number;
};

type Undelegate = {
  kind: string;
  val: Validator;
  amt: number;
};

type JumpNBlocks = {
  kind: string;
  chains: Chain[];
  n: number;
  secondsPerBlock: number;
};

type Deliver = {
  kind: string;
  chain: Chain;
  numPackets: number;
};

type ConsumerSlash = {
  kind: string;
  val: Validator;
  infractionHeight: number;
  isDowntime: boolean;
};

type Snapshot = {
  h: Record<Chain, number>;
  t: Record<Chain, number>;
  tokens: number[];
  status: Status[];
  undelegationQ: Undelegation[];
  validatorQ: Unval[];
  jailed: (number | undefined)[];
  delegatorTokens: number;
  power: (number | undefined)[];
};

enum Status {
  BONDED = 'bonded',
  UNBONDING = 'unbonding',
  UNBONDED = 'unbonded',
}

/**
 * Represents undelegation logic in the staking module.
 */
interface Undelegation {
  val: Validator;
  creationHeight: number;
  completionTime: number;
  balance: number;
  initialBalance: number;
  onHold: boolean;
  opID: number;
  expired: boolean;
}

/**
 * Represents unbonding validator logic in the staking module.
 */
interface Unval {
  val: Validator;
  unbondingHeight: number;
  unbondingTime: number;
  onHold: boolean;
  opID: number;
  expired: boolean;
}

/**
 * Validator Set Change data structure
 */
interface Vsc {
  vscID: number;
  updates: Record<Validator, number>;
  downtimeSlashAcks: number[];
}

/**
 * Validator Set Change Maturity notification data structure
 */
interface VscMatured {
  vscID: number;
}

/**
 * Consumer Initiated Slash data structure
 */
interface Slash {
  val: Validator;
  vscID: number;
  isDowntime: boolean;
}

type PacketData = Vsc | VscMatured | Slash;

interface Packet {
  timeoutHeight: number;
  timeoutTimestamp: number;
  data: PacketData;
  sendHeight: number;
}

/**
 * Record a snapshot of both chain states at the height and timestamp
 * of a committed block for a chain.
 */
interface CommittedBlock {
  chain: Chain;
  h: number;
  t: number;
  snapshot: Snapshot;
}

/*
 * Used to track various semantic events that occur during model exploration.
 */

enum Event {
  REBOND_UNVAL = 'rebond_unval',
  COMPLETE_UNVAL_IN_ENDBLOCK = 'complete_unval_in_endblock',
  COMPLETE_UNVAL_NOW = 'complete_unval_now',
  SET_UNVAL_HOLD_FALSE = 'set_unval_hold_false',
  COMPLETE_UNDEL_IN_ENDBLOCK = 'complete_undel_in_endblock',
  COMPLETE_UNDEL_NOW = 'complete_undel_now',
  SET_UNDEL_HOLD_FALSE = 'set_undel_hold_false',
  INSUFFICIENT_SHARES = 'insufficient_shares',
  SLASH_UNDEL = 'slash_undel',
  JAIL = 'jail',
  SEND_DOWNTIME_SLASH_REQUEST = 'send_downtime_slash_request',
  RECEIVE_DOWNTIME_SLASH_REQUEST = 'receive_downtime_slash_request',
  RECEIVE_DOWNTIME_SLASH_ACK = 'receive_downtime_slash_ack',
  SEND_DOUBLE_SIGN_SLASH_REQUEST = 'send_double_sign_slash_request',
  CONSUMER_SEND_MATURATION = 'consumer_send_maturation',
  SEND_VSC_NOT_BECAUSE_CHANGE = 'send_vsc_not_because_change',
  SEND_VSC_WITH_DOWNTIME_ACK = 'send_vsc_with_downtime_ack',
  SEND_VSC_WITHOUT_DOWNTIME_ACK = 'send_vsc_without_downtime_ack',
  SOME_UNDELS_EXPIRED_BUT_NOT_COMPLETED = 'some_undels_expired_but_not_completed',
  SOME_UNVALS_EXPIRED_BUT_NOT_COMPLETED = 'some_unvals_expired_but_not_completed',
  RECEIVE_DOUBLE_SIGN_SLASH_REQUEST = 'receive_double_sign_slash_request',
  DOWNTIME_SLASH_REQUEST_OUTSTANDING = 'downtime_slash_request_outstanding',
  CONSUMER_UPDATE_POWER_POSITIVE = 'consumer_update_power_positive',
  CONSUMER_UPDATE_POWER_ZERO = 'consumer_update_power_zero',
}

interface TraceAction {
  action: Action;
  hLastCommit: Record<Chain, number>;
}

export {
  TraceAction,
  Event,
  CommittedBlock,
  Chain,
  Validator,
  Action,
  Delegate,
  Undelegate,
  JumpNBlocks,
  Deliver,
  ConsumerSlash,
  Snapshot,
  Status,
  Undelegation,
  Unval,
  Vsc,
  VscMatured,
  Slash,
  PacketData,
  Packet,
};
