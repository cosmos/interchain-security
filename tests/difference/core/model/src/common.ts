type Chain = 'provider' | 'consumer';

type Validator = number;

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
  willBeProcessedByStakingModule: boolean;
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
  data: PacketData;
  sendHeight: number;
}

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

type ConsumerSlash = {
  kind: string;
  val: Validator;
  infractionHeight: number;
  isDowntime: boolean;
};

type UpdateClient = {
  kind: string;
  chain: Chain;
};

type Deliver = {
  kind: string;
  chain: Chain;
  numPackets: number;
};

type EndAndBeginBlock = {
  kind: string;
  chain: Chain;
};

type InvariantSnapshot = {
  h: Record<Chain, number>;
  t: Record<Chain, number>;
  tokens: number[];
  status: Status[];
  undelegationQ: Undelegation[];
  delegatorTokens: number;
  consumerPower: (number | null)[];
  vscIDtoH: Record<number, number>;
  hToVscID: Record<number, number>;
};

/**
 * Record a snapshot of both chain states at the height and timestamp
 * of a committed block for a chain.
 */
interface CommittedBlock {
  chain: Chain;
  invariantSnapshot: InvariantSnapshot;
}

/**
 * A partial snapshot of model state. It is the state
 * needed to check that the SUT is behaving correctly
 * when compared to the model.
 * 
 * NOTE: This is not a complete snapshot of the model state
 * because not all of the data is needed, and the space
 * needed adds up quickly. Also, a concise representation
 * makes traces much more readable and easier to debug
 * by inspection.
 * 
 * Fields are optional because not of the state is interesting
 * for all of the possible actions. This could be achieved
 * with a union type.
 */
interface PartialState {
  h?: number; // Chain local height
  t?: number; // Chain local timestamp
  tokens?: number[];
  delegation?: number[];
  delegatorTokens?: number;
  jailed?: (number | null)[];
  status?: Status[];
  consumerPower?: (number | null)[];
  outstandingDowntime?: boolean[];
}

interface TraceAction {
  ix: number;
  action: Action;
  partialState: PartialState;
}

/**
 * The initial state of a new model instances.
 * 
 * See model.ts for details of each field.
 */
type ModelInitState = {
  h: Record<Chain, number>;
  t: Record<Chain, number>;
  staking: {
    delegation: number[];
    tokens: number[];
    status: Status[];
    undelegationQ: Undelegation[];
    validatorQ: Unval[];
    jailed: (number | null)[];
    delegatorTokens: number;
    opID: number;
    changes: Record<Validator, number>;
    lastVals: Validator[];
    lastTokens: number[];
  };
  ccvC: {
    hToVscID: Record<number, number>;
    pendingChanges: Record<Validator, number>[];
    maturingVscs: Map<number, number>;
    outstandingDowntime: boolean[];
    consumerPower: (number | null)[];
  };
  ccvP: {
    initialHeight: number;
    vscID: number;
    vscIDtoH: Record<number, number>;
    vscIDtoOpIDs: Map<number, number[]>;
    downtimeSlashAcks: number[];
    tombstoned: boolean[];
    matureUnbondingOps: number[];
    queue: (Slash | VscMatured)[];
  };
};

export {
  ModelInitState,
  PartialState,
  TraceAction,
  CommittedBlock,
  Chain,
  Validator,
  Action,
  Delegate,
  Undelegate,
  ConsumerSlash,
  UpdateClient,
  Deliver,
  EndAndBeginBlock,
  InvariantSnapshot,
  Status,
  Undelegation,
  Unval,
  Vsc,
  VscMatured,
  Slash,
  PacketData,
  Packet,
};
