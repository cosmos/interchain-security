/*
Matches https://github.com/cosmos/ibc/tree/5ea902172b20d53e209f8c1fda9b11d005d9c110
*/

import _ from 'underscore';
import { Event } from './events.js';
import { Blocks } from './properties.js';
import cloneDeep from 'clone-deep';

import {
  P,
  C,
  UNBONDING_SECONDS,
  NUM_VALIDATORS,
  MAX_VALIDATORS,
  ZERO_TIMEOUT_HEIGHT,
  CCV_TIMEOUT_TIMESTAMP,
  SLASH_DOUBLESIGN,
  SLASH_DOWNTIME,
  JAIL_SECONDS,
  BLOCK_SECONDS,
  TOKEN_SCALAR,
  INITIAL_DELEGATOR_TOKENS,
  TRUSTING_SECONDS,
} from './constants.js';

enum Status {
  BONDED = 'bonded',
  UNBONDING = 'unbonding',
  UNBONDED = 'unbonded',
}

export interface Undelegation {
  val;
  creationHeight;
  completionTime;
  balance;
  initialBalance;
  onHold;
  opID;
  expired;
}

export interface Unval {
  val;
  unbondingHeight;
  unbondingTime;
  onHold;
  opID;
  expired;
}

interface Vsc {
  vscID;
  updates;
  slashAcks;
}

interface VscMatured {
  vscID;
}

interface Slash {
  val;
  power;
  vscID;
  isDowntime;
}

interface Packet {
  timeoutHeight;
  timeoutTimestamp;
  data;
  sendHeight;
}

class Outbox {
  model;
  chain;
  fifo: [Packet, number][];
  constructor(model, chain) {
    this.model = model;
    this.chain = chain;
    this.fifo = [];
  }
  static createPacket(data, sendHeight): Packet {
    const zeroTimeoutHeight = ZERO_TIMEOUT_HEIGHT;
    const ccvTimeoutTimestamp = CCV_TIMEOUT_TIMESTAMP;
    return {
      timeoutHeight: zeroTimeoutHeight,
      timeoutTimestamp: ccvTimeoutTimestamp,
      data,
      sendHeight: sendHeight,
    };
  }
  add = (data) => {
    this.fifo.push([
      Outbox.createPacket(data, this.model.h[this.chain]),
      0,
    ]);
  };
  isEmpty = () => {
    return 0 === this.fifo.filter((e) => 1 < e[1]).length;
  };
  consume = (): Packet[] => {
    const [available, unavailable] = _.partition(
      this.fifo,
      (e) => 1 < e[1],
    );
    this.fifo = unavailable;
    return available.map((e) => e[0]);
  };
  commit = () => {
    this.fifo = this.fifo.map((e) => [e[0], e[1] + 1]);
  };
}

class Staking {
  m;
  // the number of shares the delegator has in the validator
  // simply hardcoded to match what driver starts with
  // denominated in shares
  delegation = [
    4 * TOKEN_SCALAR,
    3 * TOKEN_SCALAR,
    2 * TOKEN_SCALAR,
    1 * TOKEN_SCALAR,
  ];
  // tokens = shares before any slashing or rewards happen
  // 1 token is self delegated by validators
  // denominated in tokens, but use 1-1 exchange rate
  tokens: number[] = this.delegation.map((it) => it + 1 * TOKEN_SCALAR);
  // validator status
  status = [
    Status.BONDED,
    Status.BONDED,
    Status.UNBONDED,
    Status.UNBONDED,
  ];
  undelegationQ: Undelegation[] = [];
  validatorQ: Unval[] = [];
  jailed: number | undefined[] = new Array(NUM_VALIDATORS).fill(
    undefined,
  );
  delegatorTokens: number = INITIAL_DELEGATOR_TOKENS;
  // used to track unbonding and redelegation entries, as well as
  // map to unbonding validators, in order to track onHold
  opID = 0;
  // used to compute val set changes
  // maps validators to power
  changes = {};

  newVals = () => {
    const valid = (i): boolean =>
      1 <= this.tokens[i] && this.jailed[i] === undefined;
    let vals = _.range(NUM_VALIDATORS);
    vals = _.sortBy(vals, (i) => -this.tokens[i]);
    vals = vals.filter(valid);
    return vals.slice(0, MAX_VALIDATORS);
  };

  // validators of last block (lastValidators)
  lastVals = this.newVals();
  // required for computation of changes;
  lastTokens = _.clone(this.tokens);

  constructor(model) {
    this.m = model;
  }

  endBlock = () => {
    // Undelegations
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
    this.delegatorTokens += completedUndels.reduce(
      (x, e) => x + e.balance,
      0,
    );
    // Validators
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
    const newUnvals = [];
    _.difference(oldVals, newVals)
      .sort((a, b) => a - b)
      .forEach((i) => {
        const unval: Unval = {
          val: i,
          unbondingHeight: this.m.h[P],
          unbondingTime: this.m.t[P] + UNBONDING_SECONDS,
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
    this.lastVals = newVals;
    this.lastTokens = _.clone(this.tokens);
  };

  delegate = (val, amt) => {
    if (this.tokens[val] === 0 && 0 < this.shares(val)) {
      this.m.events.push(Event.INVALID_EX_RATE);
      return;
    }
    const issuedShares = Math.floor(
      (this.shares(val) * amt) / this.tokens[val],
    );
    this.delegatorTokens -= amt;
    this.tokens[val] += amt;
    this.delegation[val] += issuedShares;
  };
  undelegate = (val, amt) => {
    if (this.tokens[val] < 1) {
      this.m.events.push(Event.INSUFFICIENT_TOKENS);
      return;
    }
    const shares = Math.floor(
      (this.shares(val) * amt) / this.tokens[val],
    );
    if (this.delegation[val] < shares) {
      this.m.events.push(Event.INSUFFICIENT_SHARES);
      return;
    }
    const issuedTokens = Math.floor(
      (shares * this.tokens[val]) / this.shares(val),
    );
    this.tokens[val] -= issuedTokens;
    this.delegation[val] -= shares;
    const und: Undelegation = {
      val: val,
      creationHeight: this.m.h[P],
      completionTime: this.m.t[P] + UNBONDING_SECONDS,
      balance: issuedTokens,
      initialBalance: issuedTokens,
      onHold: true,
      opID: this.opID,
      expired: false,
    };
    this.undelegationQ.push(und);
    this.m.ccvP.afterUnbondingInitiated(this.opID);
    this.opID += 1;
  };
  slash = (val, infractionHeight, power, factor) => {
    const valid = (e): boolean =>
      e.val === val &&
      infractionHeight <= e.creationHeight &&
      (this.m.t[P] < e.completionTime || e.onHold);
    const ubds: Undelegation[] = this.undelegationQ.filter(valid);
    // TODO: check rounding
    const amt = Math.floor(power * factor);
    let remaining = amt;
    if (infractionHeight < this.m.h[P]) {
      ubds.forEach((e) => {
        this.m.events.push(Event.SLASH_UNDEL);
        const slashed = Math.floor(factor * e.initialBalance);
        remaining -= slashed;
        e.balance = Math.max(0, e.balance - slashed);
      });
    }
    const toBurn = Math.min(Math.max(remaining, 0), this.tokens[val]);
    this.tokens[val] -= toBurn;
    if (0 < toBurn) {
      this.m.events.push(Event.SLASH_VAL);
    }
  };
  jailUntil = (val, timestamp) => {
    this.jailed[val] = timestamp;
    this.m.events.push(Event.JAIL);
  };
  shares = (val) => {
    return this.delegation[val] + 1 * TOKEN_SCALAR;
  };
  unbondingCanComplete = (opID) => {
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
  // TODO: I should check this
  initialHeight = 0;
  vscID = 0;
  vscIDtoH = {};
  vscIDtoOpIDs = new Map();
  downtimeSlashReqs = [];
  constructor(model) {
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
      if (0 < this.downtimeSlashReqs.length) {
        this.m.events.push(Event.SEND_VSC_WITH_DOWNTIME_ACK);
      } else {
        this.m.events.push(Event.SEND_VSC_WITHOUT_DOWNTIME_ACK);
      }
      const data: Vsc = {
        vscID: this.vscID,
        updates: valUpdates,
        slashAcks: this.downtimeSlashReqs,
      };
      this.downtimeSlashReqs = [];
      this.m.outbox[P].add(data);
    }
    this.vscID += 1;
  };
  onReceive = (data) => {
    // It's sufficient to use isDowntime field as differentiator
    if ('isDowntime' in data) {
      this.onReceiveSlash(data);
    } else {
      this.onReceiveVSCMatured(data);
    }
  };
  onReceiveVSCMatured = (data: VscMatured) => {
    if (this.vscIDtoOpIDs.has(data.vscID)) {
      this.vscIDtoOpIDs.get(data.vscID).forEach((opID) => {
        this.m.staking.unbondingCanComplete(opID);
      });
      this.vscIDtoOpIDs.delete(data.vscID);
    }
  };
  onReceiveSlash = (data: Slash) => {
    if (data.isDowntime) {
      this.m.events.push(Event.RECEIVE_DOWNTIME_SLASH_REQUEST);
    } else {
      this.m.events.push(Event.RECEIVE_DOUBLE_SIGN_SLASH_REQUEST);
    }

    const infractionHeight =
      data.vscID === 0 ? this.initialHeight : this.vscIDtoH[data.vscID];
    const factor = data.isDowntime ? SLASH_DOWNTIME : SLASH_DOUBLESIGN;

    this.m.staking.slash(data.val, infractionHeight, data.power, factor);
    this.m.staking.jailUntil(data.val, this.m.t[P] + JAIL_SECONDS);
    if (data.isDowntime) {
      this.downtimeSlashReqs.push(data.val);
    }
  };
  afterUnbondingInitiated = (opID) => {
    if (!this.vscIDtoOpIDs.has(this.vscID)) {
      this.vscIDtoOpIDs.set(this.vscID, []);
    }
    this.vscIDtoOpIDs.get(this.vscID).push(opID);
  };
}

class CCVConsumer {
  m;
  hToVscID = { 0: 0, 1: 0 };
  pendingChanges: Map<number, number>[] = [];
  maturingVscs: Map<number, number> = new Map();
  outstandingDowntime = new Array(NUM_VALIDATORS).fill(false);
  power: number | undefined[] = new Array(NUM_VALIDATORS).fill(undefined);

  constructor(model) {
    this.m = model;
    this.m.staking.lastVals.forEach((i) => {
      this.power[i] = this.m.staking.tokens[i];
    });
  }
  beginBlock = () => {
    this.hToVscID[this.m.h[C] + 1] = this.hToVscID[this.m.h[C]];
  };
  endBlock = () => {
    // unbond matured
    const matured = (() => {
      const ret = [];
      this.maturingVscs.forEach((time, vscID) => {
        if (time <= this.m.t[C]) {
          ret.push(vscID);
        }
      });
      return ret;
    })();
    if (matured.length < this.maturingVscs.size) {
      this.m.events.push(Event.CONSUMER_NOT_ALL_MATURED);
    }
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
      const ret = new Map();
      this.pendingChanges.forEach((updates) => {
        _.keys(updates).forEach((k) => {
          ret.set(k, updates[k]);
        });
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
  onReceive = (data) => {
    this.onReceiveVSC(data);
  };
  onReceiveVSC = (data: Vsc) => {
    this.hToVscID[this.m.h[C] + 1] = data.vscID;
    this.pendingChanges.push(data.updates);
    this.maturingVscs.set(data.vscID, this.m.t[C] + UNBONDING_SECONDS);
    data.slashAcks.forEach((val) => {
      this.m.events.push(Event.RECEIVE_DOWNTIME_SLASH_ACK);
      this.outstandingDowntime[val] = false;
    });
  };
  sendSlashRequest = (val, power, infractionHeight, isDowntime) => {
    if (isDowntime && this.outstandingDowntime[val]) {
      this.m.events.push(Event.DOWNTIME_SLASH_REQUEST_OUTSTANDING);
      return;
    }
    const data: Slash = {
      val,
      power,
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

class Model {
  T = 0;
  h = _.object([
    [P, 0],
    [C, 0],
  ]) as { provider: number; consumer: number };
  t = _.object([
    [P, 0],
    [C, 0],
  ]);
  outbox = {};
  staking = undefined;
  ccvP = undefined;
  ccvC = undefined;
  blocks = undefined;
  events = undefined;
  mustBeginBlock = {};

  lastUpdateClient = _.object([
    [P, 0],
    [C, 0],
  ]) as { provider: number; consumer: number };

  constructor(blocks: Blocks, events: Event[]) {
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
    this.mustBeginBlock[P] = true;
    this.mustBeginBlock[C] = true;
  }

  snapshot = () => {
    return cloneDeep({
      tokens: this.staking.tokens,
      undelegationQ: this.staking.undelegationQ,
      validatorQ: this.staking.validatorQ,
      status: this.staking.status,
      jailed: this.staking.jailed,
      delegatorTokens: this.staking.delegatorTokens,
      outbox: { P: this.outbox[P].fifo, C: this.outbox[C].fifo },
      power: this.ccvC.power,
      h: this.h,
      t: this.t,
    });
  };
  hasUndelivered = (chain): boolean => {
    return !this.outbox[chain === P ? C : P].isEmpty();
  };
  updateClient = (chain) => {
    if (this.lastUpdateClient[chain] + TRUSTING_SECONDS < this.t[chain]) {
      throw 'EXPIRED! - not supposed to happen. Bad model.';
    }
    this.lastUpdateClient[chain] = this.t[chain];
  };
  idempotentBeginBlock = (chain) => {
    if (this.mustBeginBlock[chain]) {
      this.mustBeginBlock[chain] = false;
      this.h[chain] += 1;
      this.t[chain] = this.T;
      this.updateClient(chain);
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
  endBlock = (chain) => {
    this.idempotentBeginBlock(chain);
    if (chain === P) {
      this.staking.endBlock();
      this.ccvP.endBlock();
    }
    if (chain === C) {
      this.ccvC.endBlock();
    }
    this.outbox[chain].commit();
    this.blocks.commitBlock(chain, this.snapshot());
    this.mustBeginBlock[chain] = true;
  };
  increaseSeconds = (seconds) => {
    this.T += seconds;
  };
  jumpNBlocks = (
    n: number,
    chains: string[],
    secondsPerBlock: number,
  ) => {
    for (let i = 0; i < n; i++) {
      chains.forEach(this.endBlock);
      this.increaseSeconds(secondsPerBlock);
    }
  };
  deliver = (chain: string) => {
    this.idempotentBeginBlock(chain);
    this.updateClient(chain);
    if (chain === P) {
      this.outbox[C].consume().forEach((p) => {
        this.blocks.partialOrder.deliver(P, p.sendHeight, this.h[P]);
        this.ccvP.onReceive(p.data);
      });
    }
    if (chain === C) {
      this.outbox[P].consume().forEach((p) => {
        this.blocks.partialOrder.deliver(C, p.sendHeight, this.h[C]);
        this.ccvC.onReceive(p.data);
      });
    }
  };
  providerSlash = (
    val: number,
    infractionHeight: number,
    power: number,
    factor: number,
  ) => {
    this.idempotentBeginBlock(P);
    this.staking.slash(val, infractionHeight, power, factor);
  };
  consumerSlash = (
    val: number,
    power: number,
    infractionHeight: number,
    isDowntime: boolean,
  ) => {
    this.idempotentBeginBlock(C);
    this.ccvC.sendSlashRequest(val, power, infractionHeight, isDowntime);
  };
}

export { Outbox, Model, Status };
