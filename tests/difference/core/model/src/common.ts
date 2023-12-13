type Chain = 'provider' | 'consumer';

type Validator = number;

enum Status {
  BONDED = 'bonded',
  UNBONDING = 'unbonding',
  UNBONDED = 'unbonded',
}

/**
 * All the data needed to represent an undelegation occurring
 * in the sdk staking module.
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
 * All the data needed to represent an unbonding validator
 * occurring in the sdk staking module.
 */
interface Unval {
  val: Validator;
  unbondingHeight: number;
  unbondingTime: number;
  onHold: boolean;
  opID: number;
}

/**
 * A representation of the validator set change data structure
 * sent from the provider to the consumer.
 */
interface Vsc {
  vscID: number;
  updates: Record<Validator, number>;
  downtimeSlashAcks: number[];
}

/**
 * Validator Set Change Maturity notification data structure
 */
interface VscMaturity {
  vscID: number;
}

/**
 * A representation of the packet sent by the consumer to the
 * provider when slashing.
 */
interface ConsumerInitiatedSlashPacketData {
  val: Validator;
  vscID: number;
  isDowntime: boolean;
}

type PacketData = Vsc | VscMaturity | ConsumerInitiatedSlashPacketData;

interface Packet {
  data: PacketData;
  // Necessary to deduce a partial order between the provider
  // and consumer chain, as dictated by packet sending and
  // receiving.
  sendHeight: number;
}

interface Action {
  // A tag to identify the action type
  kind: string;
}

type Delegate = {
  kind: string;
  val: Validator; // Validator to delegate to
  amt: number; // Amount to delegate
};

type Undelegate = {
  kind: string;
  val: Validator; // Validator to undelegate from
  amt: number; // Max amount to undelegate
};

type ConsumerSlash = {
  kind: string;
  val: Validator; // Validator to slash
  infractionHeight: number; // Height of the infraction on consumer
  isDowntime: boolean; // Whether the slash is for downtime (or double sign)
};

type UpdateClient = {
  kind: string;
  // The chain who will receive the light client header TX
  // (details not modelled explicitly)
  chain: Chain;
};

type Deliver = {
  kind: string;
  // The chain who will receive packets which have been sent to it
  chain: Chain;
  // The MAX number of packets to deliver, from those available
  numPackets: number;
};

type EndAndBeginBlock = {
  kind: string;
  // Which chain will end and begin a block?
  chain: Chain;
};

/**
 * A snapshot of a portion of the model state at the time
 * that a block is committed on one of the chains. 
 * 
 * The state is exactly the state that is needed to check
 * system properties.
 */
type PropertiesSystemState = {
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
  propertiesSystemState: PropertiesSystemState;
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
    queue: (ConsumerInitiatedSlashPacketData | VscMaturity)[];
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
  PropertiesSystemState,
  Status,
  Undelegation,
  Unval,
  Vsc,
  VscMaturity,
  ConsumerInitiatedSlashPacketData,
  PacketData,
  Packet,
};
