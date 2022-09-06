import * as fs from 'fs';
import _ from 'underscore';
import timeSpan from 'time-span';
import cloneDeep from 'clone-deep';
import {
  BlockHistory,
  stakingWithoutSlashing,
  bondBasedConsumerVotingPower,
} from './properties.js';
import { Model } from './model.js';
import {
  createSmallSubsetOfCoveringTraces,
  dumpTrace,
  forceMakeEmptyDir,
  logEventData,
} from './traceUtil.js';

import {
  Action,
  Undelegate,
  Delegate,
  ConsumerSlash,
  UpdateClient,
  Deliver,
  EndAndBeginBlock,
  TraceAction,
  Chain,
  Consequence,
} from './common.js';

import {
  P,
  C,
  NUM_VALIDATORS,
  DELEGATE_AMT_MIN,
  DELEGATE_AMT_MAX,
  UNDELEGATE_AMT_MIN,
  UNDELEGATE_AMT_MAX,
  ISDOWNTIME_PROBABILITY,
  TRUSTING_SECONDS,
  BLOCK_SECONDS,
  MAX_NUM_PACKETS_FOR_DELIVER,
  Event,
  MODEL_INIT_STATE,
} from './constants.js';

class ActionGenerator {
  model;
  // was the validator slashed?
  didSlash = new Array(NUM_VALIDATORS).fill(false);
  // the timestamp contained in the latest trusted header
  tLastTrustedHeader = { provider: 0, consumer: 0 };
  // the timestamp of the last committed block
  tLastCommit = { provider: 0, consumer: 0 };

  constructor(model: Model) {
    this.model = model;
  }

  create = (): Action => {
    const kind = _.sample([
      'Delegate',
      'Undelegate',
      'ConsumerSlash',
      'EndAndBeginBlock',
      'Deliver',
      'UpdateClient',
    ]);
    if (kind === 'Delegate') {
      return {
        kind,
        val: _.random(0, NUM_VALIDATORS - 1),
        amt: _.random(DELEGATE_AMT_MIN, DELEGATE_AMT_MAX),
      } as Delegate;
    }
    if (kind === 'Undelegate') {
      return {
        kind,
        val: _.random(0, NUM_VALIDATORS - 1),
        amt: _.random(UNDELEGATE_AMT_MIN, UNDELEGATE_AMT_MAX),
      } as Undelegate;
    }
    if (kind === 'ConsumerSlash') {
      return {
        kind,
        val: _.random(0, NUM_VALIDATORS - 1),
        infractionHeight: Math.floor(Math.random() * this.model.h[C]),
        isDowntime: Math.random() < ISDOWNTIME_PROBABILITY,
      } as ConsumerSlash;
    }
    if (kind === 'UpdateClient') {
      return { kind, chain: _.sample([P, C]) as Chain } as UpdateClient;
    }
    if (kind === 'Deliver') {
      return {
        kind,
        chain: _.sample([P, C]) as Chain,
        numPackets: _.random(1, MAX_NUM_PACKETS_FOR_DELIVER),
      } as Deliver;
    }
    if (kind === 'EndAndBeginBlock') {
      return {
        kind,
        chain: _.sample([P, C]) as Chain,
      } as EndAndBeginBlock;
    }
    throw `kind doesn't match`;
  };

  valid = (a: Action): boolean => {
    if (a.kind === 'Delegate') {
      return true;
    }
    if (a.kind === 'Undelegate') {
      return true;
    }
    if (a.kind === 'ConsumerSlash') {
      return 2 <= this.didSlash.filter((x) => !x).length;
    }
    if (a.kind === 'UpdateClient') {
      return true;
    }
    if (a.kind === 'Deliver') {
      return true;
    }
    if (a.kind === 'EndAndBeginBlock') {
      const chain = (a as EndAndBeginBlock).chain;
      return (
        this.model.t[chain] + BLOCK_SECONDS <
        this.tLastTrustedHeader[chain] + TRUSTING_SECONDS
      );
    }
    throw `kind doesn't match`;
  };

  /**
   * Update internal state to inform rule based action generation
   * and prevent generating traces which over approximate the system.
   * e.g. traces that expire the light clients or jail all validators.
   * @param a action
   */
  do = (a: Action) => {
    // Update internal state to prevent jailing all validators
    if (a.kind === 'ConsumerSlash') {
      this.didSlash[(a as ConsumerSlash).val] = true;
    }
    // Update internal state to prevent expiring light clients
    // Client is also updated for Deliver, because this is needed in practice
    // for SUT.
    if (a.kind === 'UpdateClient' || a.kind === 'Deliver') {
      const chain = (a as UpdateClient).chain;
      if (
        this.tLastTrustedHeader[chain] + TRUSTING_SECONDS <=
        this.model.t[chain]
      ) {
        // Sanity check to make sure client cannot expire
        throw 'Client expired (updateClient), model is not written correctly.';
      }
      this.tLastTrustedHeader[chain] =
        this.tLastCommit[chain == P ? C : P];
    }
    // Update internal state to prevent expiring light clients
    if (a.kind === 'EndAndBeginBlock') {
      const chain = (a as EndAndBeginBlock).chain;
      this.tLastCommit[chain] = this.model.t[chain];
    }
  };

  /**
   * @returns A valid model action.
   */
  get = () => {
    /* eslint no-constant-condition: 1*/
    while (true) {
      // Ok because some action is always valid
      const a = this.create();
      if (this.valid(a)) {
        this.do(a);
        return a;
      }
    }
  };
}

/**
 * Executes an action against the model, thereby updating the model state.
 * @param model The model instance
 * @param action The action to be executed against the model
 */
function doAction(model: Model, action: Action): Consequence {
  const kind = action.kind;
  if (kind === 'Delegate') {
    const a = action as Delegate;
    model.delegate(a.val, a.amt);
    return {
      h: model.h[P],
      t: model.t[P],
      tokens: model.staking.tokens,
      delegation: model.staking.delegation,
      delegatorTokens: model.staking.delegatorTokens,
    };
  }
  if (kind === 'Undelegate') {
    const a = action as Undelegate;
    model.undelegate(a.val, a.amt);
    return {
      h: model.h[P],
      t: model.t[P],
      tokens: model.staking.tokens,
      delegation: model.staking.delegation,
      delegatorTokens: model.staking.delegatorTokens,
    };
  }
  if (kind === 'ConsumerSlash') {
    const a = action as ConsumerSlash;
    model.consumerSlash(a.val, a.infractionHeight, a.isDowntime);
    return {
      h: model.h[C],
      t: model.t[C],
      outstandingDowntime: model.ccvC.outstandingDowntime,
    };
  }
  if (kind === 'UpdateClient') {
    const a = action as UpdateClient;
    model.updateClient(a.chain);
    return {};
  }
  if (kind === 'Deliver') {
    const a = action as Deliver;
    model.deliver(a.chain, a.numPackets);
    if (a.chain === P) {
      return {
        h: model.h[P],
        t: model.t[P],
        tokens: model.staking.tokens,
        delegation: model.staking.delegation,
        delegatorTokens: model.staking.delegatorTokens,
        jailed: model.staking.jailed,
        status: model.staking.status,
      };
    }
    if (a.chain === C) {
      return {
        h: model.h[C],
        t: model.t[C],
        consumerPower: model.ccvC.consumerPower,
        outstandingDowntime: model.ccvC.outstandingDowntime,
      };
    }
  }
  if (kind === 'EndAndBeginBlock') {
    const a = action as EndAndBeginBlock;
    model.endAndBeginBlock(a.chain);
    if (a.chain === P) {
      return {
        h: model.h[P],
        t: model.t[P],
        tokens: model.staking.tokens,
        delegation: model.staking.delegation,
        delegatorTokens: model.staking.delegatorTokens,
        jailed: model.staking.jailed,
        status: model.staking.status,
      };
    }
    if (a.chain === C) {
      return {
        h: model.h[C],
        t: model.t[C],
        consumerPower: model.ccvC.consumerPower,
        outstandingDowntime: model.ccvC.outstandingDowntime,
      };
    }
  }
  throw 'Action kind not recognized';
}

/**
 * Generates traces by repeatedly creating new model instances
 * and executing randomly generated actions against them.
 * The trace consists of data including the actions taken, and the
 * successive model states that result from the actions. Additional
 * data is included
 * @param seconds Duration to generate traces.
 * @param checkProperties If true, will check properties and only write trace
 * if property is violated.
 */
function gen(seconds: number, checkProperties: boolean) {
  // Compute millis run time
  const runTimeMillis = seconds * 1000;
  let elapsedMillis = 0;
  // Number of actions to execute against each model instance
  // Free parameter!
  const NUM_ACTIONS = 200;
  // Directory to output traces in json format
  const DIR = 'traces/';
  forceMakeEmptyDir(DIR);
  let i = 0;
  // Track the model events that occur during the generation process
  // this data is used to check that all events are emitted by some
  // trace.
  const allEvents = [];
  while (elapsedMillis < runTimeMillis) {
    i += 1;
    const end = timeSpan();
    ////////////////////////
    const hist = new BlockHistory();
    // Store all events emitted during trace execution
    const events: Event[] = [];
    const model = new Model(hist, events, cloneDeep(MODEL_INIT_STATE));
    const actionGenerator = new ActionGenerator(model);
    const actions: TraceAction[] = [];
    for (let j = 0; j < NUM_ACTIONS; j++) {
      const a = actionGenerator.get();
      const consequence = doAction(model, a);
      actions.push({
        ix: j,
        // Store the action taken
        action: a,
        // Store the consequence of the action for model comparison
        consequence: cloneDeep(consequence),
      });
      if (checkProperties) {
        // Checking properties is flagged because it is computationally
        // expensive.
        if (!bondBasedConsumerVotingPower(hist)) {
          dumpTrace(`${DIR}trace_${i}.json`, actions, events);
          throw 'bondBasedConsumerVotingPower property failure, trace written.';
        }
        if (!stakingWithoutSlashing(hist)) {
          dumpTrace(`${DIR}trace_${i}.json`, actions, events);
          throw 'stakingWithoutSlashing property failure, trace written.';
        }
      }
    }
    if (!checkProperties) {
      // Write the trace to file, along with metadata.
      dumpTrace(`${DIR}trace_${i}.json`, actions, events);
    }
    // Accumulate all events
    allEvents.push(...events);
    ////////////////////////
    elapsedMillis += end.rounded();
    // Log progress stats
    if (i % 10000 === 0) {
      console.log(
        `done ${i}, actions per second ${
          (i * NUM_ACTIONS) / (elapsedMillis / 1000)
        }`,
      );
    }
  }
  logEventData(allEvents);
}

/**
 * Replays a list of actions against a new model instance.
 * This function is best used to debug the model or to debug
 * a failing test against the SUT. In this manner it is possible
 * to step through the model execution and the SUT execution of trace
 * side-by-side.
 * The model is deterministic, thus a fixed list of actions always
 * results in the same behavior and model states.
 * @param actions
 */
function replay(actions: TraceAction[]) {
  const hist = new BlockHistory();
  const events: Event[] = [];
  const model = new Model(hist, events, MODEL_INIT_STATE);
  const actionGenerator = new ActionGenerator(model);
  for (let i = 0; i < actions.length; i++) {
    const a = actions[i];
    console.log(a);
    actionGenerator.do(a.action);
    doAction(model, a.action);
    bondBasedConsumerVotingPower(hist);
  }
}

/**
 * @param fn filename of the file containing the json traces
 * @param ix the index of the trace in the json
 * @param numActions The number of actions to replay from the trace. If numActions
 * is less than the length of the trace, then execution will complete before
 * the entire trace has been executed. This helps with debugging because it makes
 * logs shorter.
 */
function replayFile(fn: string, ix: number, numActions: number) {
  const traces = JSON.parse(fs.readFileSync(fn, 'utf8'));
  const trace = ix !== undefined ? traces[ix] : traces[0];
  const traceActions = trace.actions as TraceAction[];
  const actions = traceActions.slice(0, numActions);
  replay(actions);
}

console.log(`running main`);

/*
 * Generate new traces and write them to files, for <seconds> seconds.
 *
 * yarn start gen <seconds>
 */
if (process.argv[2] === 'gen') {
  console.log(`gen`);
  const seconds = parseInt(process.argv[3]);
  gen(seconds, false);
} else if (process.argv[2] === 'properties') {
  /*
   * Check properties of the model for <seconds> seconds.
   *
   * yarn start properties <seconds>
   */
  console.log(`properties`);
  const seconds = parseInt(process.argv[3]);
  gen(seconds, true);
} else if (process.argv[2] === 'subset') {
  /*
   * Creates a trace file containing several traces, in a way that ensures
   * each interesting model event is emitted by some trace.
   *
   * yarn start subset <output file abs path> <num event instances (optional)>
   */
  console.log(`createSmallSubsetOfCoveringTraces`);
  const outFile = process.argv[3];
  let eventInstances = 20;
  if (3 < process.argv.length) {
    eventInstances = parseInt(process.argv[4]);
  }
  createSmallSubsetOfCoveringTraces(outFile, eventInstances);
} else if (process.argv[2] === 'replay') {
  /*
   * Replay a trace from a a file, up to a given number of actions.
   *
   * yarn start replay <filename> <list index> <num actions>
   */
  console.log(`replay`);
  const [fn, traceNum, numActions] = process.argv.slice(3, 6);
  replayFile(fn, parseInt(traceNum), parseInt(numActions));
} else {
  console.log(`did not execute any function`);
}

console.log(`finished running main`);

export { gen };
