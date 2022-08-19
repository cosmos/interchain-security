import _ from 'underscore';
import { Event } from './events.js';
import { BlockHistory } from './properties.js';
import { Sanity } from './sanity.js';
import cloneDeep from 'clone-deep';

import {
  P,
  C,
  UNBONDING_SECONDS_P,
  UNBONDING_SECONDS_C,
  NUM_VALIDATORS,
  MAX_VALIDATORS,
  ZERO_TIMEOUT_HEIGHT,
  CCV_TIMEOUT_TIMESTAMP,
  JAIL_SECONDS,
  BLOCK_SECONDS,
  TOKEN_SCALAR,
  INITIAL_DELEGATOR_TOKENS,
} from './constants.js';

type Chain = 'provider' | 'consumer'

type Validator = number

enum Status {
  BONDED = 'bonded',
  UNBONDING = 'unbonding',
  UNBONDED = 'unbonded',
}

/**
 * Represents undelegation logic in the staking module.
 */
export interface Undelegation {
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
export interface Unval {
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
 * Store outbound packets in FIFO order from a given chain.
 * The number of block commits for each packet is stored,
 * and deliverable packets can be consumed once they are sufficiently
 * committed. This mimics real IBC connections.
 */
class Outbox {
  model;
  chain;
  // [packet, num commits]
  fifo: [Packet, number][];
  constructor(model: Model, chain: Chain) {
    this.model = model;
    this.chain = chain;
    this.fifo = [];
  }
  static createPacket(data: PacketData, sendHeight: number): Packet {
    const zeroTimeoutHeight = ZERO_TIMEOUT_HEIGHT;
    const ccvTimeoutTimestamp = CCV_TIMEOUT_TIMESTAMP;
    return {
      timeoutHeight: zeroTimeoutHeight,
      timeoutTimestamp: ccvTimeoutTimestamp,
      data,
      sendHeight: sendHeight,
    };
  }

  /**
   * Adds a packet to the outbox, with 0 commits.
   * 
   * @param data packet data
   */
  add = (data: PacketData) => {
    this.fifo.push([
      Outbox.createPacket(data, this.model.h[this.chain]),
      0,
    ]);
  };

  /**
   * Get the number of deliverable packets from this outbox.
   * A packet is deliverable if it two blocks have committed on
   * the sender chain since the packet was sent. This is as
   * per the light-client functioning.
   * 
   * @returns The number of deliverable packets.
   */
  numAvailable = (): number => {
    return this.fifo.filter((e) => 1 < e[1]).length;
  };

  /**
   * Get and internally delete deliverable packets from the outbox.
   * 
   * @param num num packets to consumer
   * @returns A list of deliverable packets
   */
  consume = (num: number): Packet[] => {
    const [available, unavailable] = _.partition(
      this.fifo,
      (e) => 1 < e[1],
    );
    const take = available.slice(0, num);
    this.fifo = available.slice(num).concat(unavailable);
    return take.map((e) => e[0]);
  };
  /**
   * Commit the packets in the outbox. Once a packet has been
   * committed twice it is available for delivery, as per the
   * ibc light-client functioning.
   */
  commit = () => {
    this.fifo = this.fifo.map((e) => [e[0], e[1] + 1]);
  };
}

class Staking {
  // Model handle
  m;
  // Validator delegations from the delegator
  // A fixed descending order is used for the initial values to allow
  // easy setup in the SUT.
  delegation = [
    4 * TOKEN_SCALAR,
    3 * TOKEN_SCALAR,
    2 * TOKEN_SCALAR,
    1 * TOKEN_SCALAR,
  ];
  // Validator tokens
  // 1 additional unit is given to prevent validators from being deleted
  // by the staking module when the delegation falls to 0.
  tokens: number[] = this.delegation.map((it) => it + 1 * TOKEN_SCALAR);
  // Validator status
  status = [
    Status.BONDED, // Bonded as per the delegation above
    Status.BONDED, // ^^
    Status.UNBONDED, // Unbonded as per MAX_VALIDATORS
    Status.UNBONDED, // ^^
  ];
  // Undelegation queue
  undelegationQ: Undelegation[] = [];
  // Unbonding validator queue
  validatorQ: Unval[] = [];
  // Validator jail timestamp
  // Undefined if validator is not jailed
  jailed: (number | undefined)[] = new Array(NUM_VALIDATORS).fill(
    undefined,
  );
  // Initial balance of delegator account.
  delegatorTokens: number = INITIAL_DELEGATOR_TOKENS;
  // Unique ID used to count unbonding and redelegation queue entries,
  // as well as unbonding validators.
  opID = 0;
  // maps validator id -> power
  // used to compute validator set changes
  changes: Record<Validator, number> = {};
  // The validators of the last block
  lastVals;
  // The number of tokens of the last block
  // Used to compute validator power changes used in VSCs
  lastTokens = _.clone(this.tokens);

  /**
   * Compute the new set of active validators
   */
  newVals = () => {
    const valid = (i: number): boolean =>
      1 <= this.tokens[i] && this.jailed[i] === undefined;
    let vals = _.range(NUM_VALIDATORS);
    // stable sort => breaks ties based on validator
    // address numerical value. This mimics staking module.
    vals = _.sortBy(vals, (i) => -this.tokens[i]);
    vals = vals.filter(valid);
    vals = vals.slice(0, MAX_VALIDATORS);
    this.m.sanity.newValSet(vals);
    return vals;
  };

  constructor(model: Model) {
    this.m = model;
    this.lastVals = this.newVals();
  }

  endBlock = () => {
    // Process undelegations
    const expiredUndels = this.undelegationQ.filter(
      (e) => e.completionTime <= this.m.t[P] && !e.expired,
    );
    expiredUndels.forEach((e: Undelegation) => (e.expired = true));
    const completedUndels = expiredUndels.filter((e) => !e.onHold);
    if (completedUndels.length < expiredUndels.length) {
      this.m.events.push(Event.SOME_UNDELS_EXPIRED_BUT_NOT_COMPLETED);
    }
    this.undelegationQ = this.undelegationQ.filter(
      (e: Undelegation) => !completedUndels.includes(e),
    );
    if (0 < completedUndels.length) {
      this.m.events.push(Event.COMPLETE_UNDEL_IN_ENDBLOCK);
    }
    // Refund completed undelegations
    this.delegatorTokens += completedUndels.reduce(
      (x, e) => x + e.balance,
      0,
    );

    // Compute the new validator set
    const oldVals = this.lastVals;
    const newVals = this.newVals();
    newVals.forEach((i) => {
      this.status[i] = Status.BONDED;
      const before = this.validatorQ.length;
      this.validatorQ = this.validatorQ.filter((e) => e.val != i);
      if (this.validatorQ.length != before) {
        this.m.events.push(Event.REBOND_UNVAL);
      }
    });

    // Process unbonding validators
    const expiredUnvals = this.validatorQ.filter(
      (e: Unval) =>
        e.unbondingTime <= this.m.t[P] &&
        e.unbondingHeight <= this.m.h[P] &&
        !e.expired,
    );
    expiredUnvals.forEach((e: Unval) => (e.expired = true));
    const completedUnvals: Unval[] = expiredUnvals.filter(
      (e) => !e.onHold,
    );
    if (completedUnvals.length < expiredUnvals.length) {
      this.m.events.push(Event.SOME_UNVALS_EXPIRED_BUT_NOT_COMPLETED);
    }
    completedUnvals.forEach((e: Unval) => {
      this.status[e.val] = Status.UNBONDED;
      this.m.events.push(Event.COMPLETE_UNVAL_IN_ENDBLOCK);
    });
    const newUnvals: Unval[] = [];
    _.difference(oldVals, newVals)
      .sort((a, b) => a - b)
      .forEach((i) => {
        const unval: Unval = {
          val: i,
          unbondingHeight: this.m.h[P],
          unbondingTime: this.m.t[P] + UNBONDING_SECONDS_P,
          onHold: true,
          opID: this.opID,
          expired: false,
        };
        newUnvals.push(unval);
        this.m.ccvP.afterUnbondingInitiated(this.opID);
        this.opID += 1;
        this.status[i] = Status.UNBONDING;
      });
    this.validatorQ = this.validatorQ.filter(
      (e) => !completedUnvals.includes(e),
    );
    this.validatorQ.push(...newUnvals);
    this.changes = {};
    newVals.forEach((i) => {
      if (this.tokens[i] != this.lastTokens[i]) {
        // validator power changed
        this.changes[i] = this.tokens[i];
      }
    });
    _.difference(newVals, oldVals)
      .sort((a, b) => a - b)
      .forEach((i) => {
        // validator bonded
        this.changes[i] = this.tokens[i];
      });
    _.difference(oldVals, newVals)
      .sort((a, b) => a - b)
      .forEach((i) => {
        // validator no longer bonded
        this.changes[i] = 0;
      });

    // Save the valset and their tokens
    // (mimics block commit)
    this.lastVals = newVals;
    this.lastTokens = _.clone(this.tokens);
  };

  delegate = (val: Validator, amt: number) => {
    this.delegatorTokens -= amt;
    this.tokens[val] += amt;
    this.delegation[val] += amt;
  };

  undelegate = (val: Validator, amt: number) => {
    if (this.delegation[val] < amt) {
      this.m.events.push(Event.INSUFFICIENT_SHARES);
      return;
    }
    this.tokens[val] -= amt;
    this.delegation[val] -= amt;
    const und: Undelegation = {
      val: val,
      creationHeight: this.m.h[P],
      completionTime: this.m.t[P] + UNBONDING_SECONDS_P,
      balance: amt,
      initialBalance: amt,
      onHold: true,
      opID: this.opID,
      expired: false,
    };
    this.undelegationQ.push(und);
    this.m.ccvP.afterUnbondingInitiated(this.opID);
    this.opID += 1;
  };

  slash = (val: Validator, infractionHeight: number) => {
    const valid = (e: Undelegation): boolean =>
      e.val === val &&
      infractionHeight <= e.creationHeight &&
      (this.m.t[P] < e.completionTime || e.onHold);
    const ubds: Undelegation[] = this.undelegationQ.filter(valid);
    if (infractionHeight < this.m.h[P]) {
      ubds.forEach(() => {
        this.m.events.push(Event.SLASH_UNDEL);
      });
    }
  };

  jailUntil = (val: Validator, timestamp: number) => {
    this.jailed[val] = timestamp;
    this.m.events.push(Event.JAIL);
  };

  unbondingCanComplete = (opID: number) => {
    {
      const e = _.find(this.validatorQ, (e) => e.opID === opID);
      if (e) {
        if (
          e.unbondingHeight < this.m.h[P] &&
          e.unbondingTime < this.m.t[P]
        ) {
          this.status[e.val] = Status.UNBONDED;
          this.validatorQ = this.validatorQ.filter((x) => x !== e);
          this.m.events.push(Event.COMPLETE_UNVAL_NOW);
        } else {
          e.onHold = false;
          this.m.events.push(Event.SET_UNVAL_HOLD_FALSE);
        }
        return;
      }
    }
    const e = _.find(this.undelegationQ, (e) => e.opID === opID);
    if (e) {
      if (e.completionTime <= this.m.t[P]) {
        this.delegatorTokens += e.balance;
        this.undelegationQ = this.undelegationQ.filter((x) => x !== e);
        this.m.events.push(Event.COMPLETE_UNDEL_NOW);
      } else {
        e.onHold = false;
        this.m.events.push(Event.SET_UNDEL_HOLD_FALSE);
      }
    }
  };

  valUpdates = () => {
    return _.clone(this.changes);
  };
}

class CCVProvider {
  m;
  initialHeight = 0;
  vscID = 0;
  vscIDtoH: Record<number, number> = {};
  vscIDtoOpIDs = new Map();
  downtimeSlashAcks: number[] = [];
  tombstoned = new Array(NUM_VALIDATORS).fill(false);

  constructor(model: Model) {
    this.m = model;
  }

  endBlock = () => {
    this.vscIDtoH[this.vscID] = this.m.h[P] + 1;
    const valUpdates = this.m.staking.valUpdates();
    const hasOps =
      this.vscIDtoOpIDs.has(this.vscID) &&
      0 < this.vscIDtoOpIDs.get(this.vscID).length;
    if (0 < _.keys(valUpdates).length || hasOps) {
      if (0 === _.keys(valUpdates).length) {
        this.m.events.push(Event.SEND_VSC_NOT_BECAUSE_CHANGE);
      }
      if (0 < this.downtimeSlashAcks.length) {
        this.m.events.push(Event.SEND_VSC_WITH_DOWNTIME_ACK);
      } else {
        this.m.events.push(Event.SEND_VSC_WITHOUT_DOWNTIME_ACK);
      }
      const data: Vsc = {
        vscID: this.vscID,
        updates: valUpdates,
        downtimeSlashAcks: this.downtimeSlashAcks,
      };
      this.downtimeSlashAcks = [];
      this.m.outbox[P].add(data);
    }
    this.vscID += 1;
  };

  onReceive = (data: PacketData) => {
    // It's sufficient to use isDowntime field as differentiator
    if ('isDowntime' in data) {
      this.onReceiveSlash(data);
    } else {
      this.onReceiveVSCMatured(data);
    }
  };

  onReceiveVSCMatured = (data: VscMatured) => {
    if (this.vscIDtoOpIDs.has(data.vscID)) {
      this.vscIDtoOpIDs.get(data.vscID).forEach((opID: number) => {
        this.m.staking.unbondingCanComplete(opID);
      });
      this.vscIDtoOpIDs.delete(data.vscID);
    }
  };

  onReceiveSlash = (data: Slash) => {
    let infractionHeight = undefined;

    if (data.vscID === 0) {
      infractionHeight = this.initialHeight;
    } else {
      infractionHeight = this.vscIDtoH[data.vscID];
    }

    if (data.isDowntime) {
      this.m.events.push(Event.RECEIVE_DOWNTIME_SLASH_REQUEST);
    } else {
      this.m.events.push(Event.RECEIVE_DOUBLE_SIGN_SLASH_REQUEST);
    }

    if (this.tombstoned[data.val]) {
      return;
    }

    this.m.staking.slash(data.val, infractionHeight);
    this.m.staking.jailUntil(data.val, this.m.t[P] + JAIL_SECONDS);
    if (data.isDowntime) {
      this.downtimeSlashAcks.push(data.val);
    } else {
      this.tombstoned[data.val] = true;
    }
  };

  afterUnbondingInitiated = (opID: number) => {
    if (!this.vscIDtoOpIDs.has(this.vscID)) {
      this.vscIDtoOpIDs.set(this.vscID, []);
    }
    this.vscIDtoOpIDs.get(this.vscID).push(opID);
  };
}

class CCVConsumer {
  m;
  hToVscID: Record<number, number> = { 0: 0, 1: 0 };
  pendingChanges: Record<Validator, number>[] = [];
  maturingVscs: Map<number, number> = new Map();
  outstandingDowntime = new Array(NUM_VALIDATORS).fill(false);
  // array of validators to power
  // value undefined if validator is not known to consumer
  power: (number | undefined)[] = new Array(NUM_VALIDATORS).fill(undefined);

  constructor(model: Model) {
    this.m = model;
    // We model an initial state in which the consumer has already
    // received an up-to-date val set from the provider.
    this.m.staking.lastVals.forEach((i) => {
      this.power[i] = this.m.staking.tokens[i];
    });
  }

  beginBlock = () => {
    this.hToVscID[this.m.h[C] + 1] = this.hToVscID[this.m.h[C]];
  };

  endBlock = () => {
    // Unbond all the matured VSCs
    const matured = (() => {
      const ret: number[] = [];
      this.maturingVscs.forEach((time, vscID) => {
        if (time <= this.m.t[C]) {
          ret.push(vscID);
        }
      });
      return ret;
    })();
    matured.forEach((vscID) => {
      const data: VscMatured = { vscID };
      this.m.events.push(Event.CONSUMER_SEND_MATURATION);
      this.m.outbox[C].add(data);
      this.maturingVscs.delete(vscID);
    });
    // gather and apply any changes
    if (this.pendingChanges.length < 1) {
      return;
    }
    const changes = (() => {
      const ret: Map<Validator, number> = new Map();
      this.pendingChanges.forEach((updates) => {
        Object.entries(updates).forEach(([val, power]) => ret.set(parseInt(val), power))
      });
      return ret;
    })();

    this.pendingChanges = [];

    changes.forEach((power, val) => {
      this.power[val] = undefined;
      if (0 < power) {
        this.m.events.push(Event.CONSUMER_UPDATE_POWER_POSITIVE);
        this.power[val] = power;
      } else {
        this.m.events.push(Event.CONSUMER_UPDATE_POWER_ZERO);
      }
    });
  };

  onReceive = (data: PacketData) => {
    this.onReceiveVSC(data as Vsc); // TODO: change!
  };

  onReceiveVSC = (data: Vsc) => {
    this.hToVscID[this.m.h[C] + 1] = data.vscID;
    this.pendingChanges.push(data.updates);
    this.maturingVscs.set(data.vscID, this.m.t[C] + UNBONDING_SECONDS_C);
    data.downtimeSlashAcks.forEach((val: number) => {
      this.m.events.push(Event.RECEIVE_DOWNTIME_SLASH_ACK);
      this.outstandingDowntime[val] = false;
    });
  };

  sendSlashRequest = (val: number, infractionHeight: number, isDowntime: boolean) => {
    if (isDowntime && this.outstandingDowntime[val]) {
      this.m.events.push(Event.DOWNTIME_SLASH_REQUEST_OUTSTANDING);
      return;
    }
    const data: Slash = {
      val,
      vscID: this.hToVscID[infractionHeight],
      isDowntime,
    };
    this.m.outbox[C].add(data);
    if (isDowntime) {
      this.m.events.push(Event.SEND_DOWNTIME_SLASH_REQUEST);
      this.outstandingDowntime[val] = true;
    } else {
      this.m.events.push(Event.SEND_DOUBLE_SIGN_SLASH_REQUEST);
    }
  };
}

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
}

class Model {
  T = 0;
  h = { provider: 0, consumer: 0 }
  t = { provider: 0, consumer: 0 }
  outbox: Record<string, Outbox>;
  staking: Staking;
  ccvP: CCVProvider;
  ccvC: CCVConsumer;
  blocks: BlockHistory;
  events: Event[];
  mustBeginBlock = { provider: true, consumer: true }
  sanity: Sanity;

  constructor(sanity: Sanity, blocks: BlockHistory, events: Event[]) {
    this.sanity = sanity;
    this.outbox[P] = new Outbox(this, P);
    this.outbox[C] = new Outbox(this, C);
    this.staking = new Staking(this);
    this.ccvP = new CCVProvider(this);
    this.ccvC = new CCVConsumer(this);
    this.blocks = blocks;
    this.events = events;
    this.blocks.partialOrder.deliver(C, 0, 0);
    this.blocks.commitBlock(P, this.snapshot());
    this.blocks.commitBlock(C, this.snapshot());
    this.increaseSeconds(BLOCK_SECONDS);
    // this.mustBeginBlock[P] = true;
    // this.mustBeginBlock[C] = true;
  }

  snapshot = (): Snapshot => {
    return cloneDeep({
      h: this.h,
      t: this.t,
      tokens: this.staking.tokens,
      status: this.staking.status,
      undelegationQ: this.staking.undelegationQ,
      validatorQ: this.staking.validatorQ,
      jailed: this.staking.jailed,
      delegatorTokens: this.staking.delegatorTokens,
      power: this.ccvC.power,
    });
  };

  idempotentBeginBlock = (chain: Chain) => {
    if (this.mustBeginBlock[chain]) {
      this.mustBeginBlock[chain] = false;
      this.h[chain] += 1;
      this.t[chain] = this.T;
      this.sanity.updateClient(chain, this.t[chain]);
      if (chain === P) {
        // No op
      }
      if (chain === C) {
        this.ccvC.beginBlock();
      }
    }
  };

  delegate = (val: number, amt: number) => {
    this.idempotentBeginBlock(P);
    this.staking.delegate(val, amt);
  };

  undelegate = (val: number, amt: number) => {
    this.idempotentBeginBlock(P);
    this.staking.undelegate(val, amt);
  };

  endBlock = (chain: Chain) => {
    this.idempotentBeginBlock(chain);
    if (chain === P) {
      this.staking.endBlock();
      this.ccvP.endBlock();
    }
    if (chain === C) {
      this.ccvC.endBlock();
    }
    this.outbox[chain].commit();
    this.sanity.commitBlock(chain, this.t[chain]);
    this.blocks.commitBlock(chain, this.snapshot());
    this.mustBeginBlock[chain] = true;
  };

  increaseSeconds = (seconds: number) => {
    this.T += seconds;
  };

  jumpNBlocks = (
    n: number,
    chains: Chain[],
    secondsPerBlock: number,
  ) => {
    for (let i = 0; i < n; i++) {
      chains.forEach(this.endBlock);
      this.increaseSeconds(secondsPerBlock);
    }
  };

  deliver = (chain: Chain, num: number) => {
    this.idempotentBeginBlock(chain);
    this.sanity.updateClient(chain, this.t[chain]);
    if (chain === P) {
      this.outbox[C].consume(num).forEach((p) => {
        this.blocks.partialOrder.deliver(P, p.sendHeight, this.h[P]);
        this.ccvP.onReceive(p.data);
      });
    }
    if (chain === C) {
      this.outbox[P].consume(num).forEach((p) => {
        this.blocks.partialOrder.deliver(C, p.sendHeight, this.h[C]);
        this.ccvC.onReceive(p.data);
      });
    }
  };

  consumerSlash = (
    val: number,
    infractionHeight: number,
    isDowntime: boolean,
  ) => {
    this.idempotentBeginBlock(C);
    this.ccvC.sendSlashRequest(val, infractionHeight, isDowntime);
  };
}

export { Outbox, Model, Status, Chain, Validator, Snapshot };
