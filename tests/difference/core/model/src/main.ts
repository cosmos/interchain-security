import * as fs from 'fs';
import _ from 'underscore';
import timeSpan from 'time-span';
import cloneDeep from 'clone-deep';
import {
  BlockHistory,
  stakingWithoutSlashing,
  bondBasedConsumerVotingPower,
  validatorSetReplication,
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
  Unjail,
  UpdateClient,
  Deliver,
  EndAndBeginBlock,
  TraceAction,
  Chain,
  PartialState,
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

/**
 * A mechanism for generating actions (API calls) in a way that
 * ensures good coverage of a range of system behaviors. In order
 * to achieve this, some bookkeeping state is kept around, that is
 * NOT state of the model, but is used to inform the action generation.
 * 
 * For example, we explore behaviors where the IBC clients of the chains
 * do not expire. To achieve this, we keep track of the last time a client
 */
class ActionGenerator {
  model;
  // Was the validator slashed? This is used to prevent jailing all validators
  // It does not make sense to jail all validators, because we know this will
  // kill the chain, and we want to explore other behaviors.
  didSlash = new Array(NUM_VALIDATORS).fill(false);
  // For each chain CHAIN, the timestamp contained in the last header from the 
  // OPPOSING chain that was trusted by the light client on CHAIN.
  // This is used to prevent the light clients from expiring.
  tLastTrustedHeader = { provider: 0, consumer: 0 };
  // For each chain CHAIN, the timestamp of the last block that was committed
  // on CHAIN.
  // This is used to prevent the light clients from expiring.
  tLastCommit = { provider: 0, consumer: 0 };

  constructor(model: Model) {
    this.model = model;
  }

  createCandidateAction = (): Action => {
    const kind = _.sample([
      'Delegate',
      'Undelegate',
      'ConsumerSlash',
      'Unjail',
      'EndAndBeginBlock',
      'Deliver',
      'UpdateClient',
    ]);
    if (kind === 'Delegate') {
      return {
        kind,
        val: _.random(0, NUM_VALIDATORS - 1), // Choose any validator
        amt: _.random(DELEGATE_AMT_MIN, DELEGATE_AMT_MAX), // An amount
      } as Delegate;
    }
    if (kind === 'Undelegate') {
      return {
        kind,
        val: _.random(0, NUM_VALIDATORS - 1), // Any validator
        amt: _.random(UNDELEGATE_AMT_MIN, UNDELEGATE_AMT_MAX), // An amount
      } as Undelegate;
    }
    if (kind === 'ConsumerSlash') {
      return {
        kind,
        val: _.random(0, NUM_VALIDATORS - 1), // Any validator
        // Any height up to the current height of the chain
        infractionHeight: Math.floor(Math.random() * this.model.h[C]),
        // Choose downtime or doublesign
        isDowntime: Math.random() < ISDOWNTIME_PROBABILITY,
      } as ConsumerSlash;
    }
    if (kind === 'Unjail') {
      return {
        kind,
        val: _.random(0, NUM_VALIDATORS - 1), // Any validator
      } as Unjail;
    }
    if (kind === 'UpdateClient') {
      return {
        kind,
        // Any chain
        chain: _.sample([P, C]) as Chain
      } as UpdateClient;
    }
    if (kind === 'Deliver') {
      return {
        kind,
        chain: _.sample([P, C]) as Chain, // Any chain
        numPackets: _.random(1, MAX_NUM_PACKETS_FOR_DELIVER), // Any number of packets
      } as Deliver;
    }
    if (kind === 'EndAndBeginBlock') {
      return {
        kind,
        chain: _.sample([P, C]) as Chain, // Any chain
      } as EndAndBeginBlock;
    }
    throw `kind doesn't match`;
  };

  validAction = (a: Action): boolean => {
    if (a.kind === 'Delegate') {
      return true;
    }
    if (a.kind === 'Undelegate') {
      return true;
    }
    if (a.kind === 'ConsumerSlash') {
      return 2 <= this.didSlash.filter((x) => !x).length;
    }
    if (a.kind === 'Unjail') {
      // only pick jailed validator
      return this.didSlash[(a as Unjail).val];
    }
    if (a.kind === 'UpdateClient') {
      return true;
    }
    if (a.kind === 'Deliver') {
      return true;
    }
    if (a.kind === 'EndAndBeginBlock') {
      // It is only possible for a chain to progress if progressing
      // will not cause its light client to expire.
      const chain = (a as EndAndBeginBlock).chain;
      return (
        // If this holds, adding BLOCK_SECONDS to the chain time
        // will not cause the the last trusted header timestamp
        // to fall outside of the trusted period.
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
    // TODO: understand why it breaks the jailing
    // and why it's not even needed
    // if (a.kind === 'Unjail') {
      // this.didSlash[(a as Unjail).val] = false;
    // }
    if (a.kind === 'UpdateClient' || a.kind === 'Deliver') {
      const chain = (a as UpdateClient).chain;
      if (
        this.tLastTrustedHeader[chain] + TRUSTING_SECONDS <=
        this.model.t[chain]
      ) {
        // This implies the client has expired. This should not happen.
        // Sanity check to make sure.
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
   * Get a sensible (valid) action, which can be executed against the model.
   * @returns A valid model action.
   */
  get = (): Action => {
    // Loop not infinite: some actions are always valid (e.g. Delegate)
    /* eslint no-constant-condition: 1*/
    while (true) {
      const a = this.createCandidateAction();
      if (this.validAction(a)) {
        // Update the internal state of the action generator
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
function doAction(model: Model, action: Action): PartialState {
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
    model.consumerInitiatedSlash(a.val, a.infractionHeight, a.isDowntime);
    return {
      h: model.h[C],
      t: model.t[C],
      outstandingDowntime: model.ccvC.outstandingDowntime,
    };
  }

  if (kind === 'Unjail') {
    const a = action as Unjail;
    model.unjail(a.val)
    return {
      h: model.h[P],
      t: model.t[P],
    };
    // Implement check according to jail until time stamp
    // validator update
    // send val update
    // slash acks
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
 * 
 * @param seconds Duration to generate traces.
 * @param checkProperties If true, will check properties and only write trace
 * if property is violated.
 */
function generateTraces(seconds: number, checkProperties: boolean) {
  // Compute millis run time
  const runTimeMillis = seconds * 1000;
  let elapsedMillis = 0;

  // Number of actions to execute against each model instance
  // Free parameter! 200 is a good default for this model.
  //
  // INFO: A number of actions MAY or MAY NOT lead to interesting
  //       system states.
  //       A very large number of actions MAY result in a state
  //       which is 'stuck': further actions change the state very little or 
  //       explore nearby areas.
  //       A very small number of actions MAY not explore the model
  //       deeply enough to uncover bugs.
  //       You should choose this number based on coverage measurements
  //       and your intuition about the model.
  const NUM_ACTIONS = 200;

  // Directory to output traces in json format
  const DIR = 'traces/';
  // Make or clear the output directory. WARNING: may delete data.
  forceMakeEmptyDir(DIR);

  let i = 0; // Used to measure operations per second

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
      const partialState = doAction(model, a);
      actions.push({
        ix: j,
        // Store the action taken
        action: a,
        // Store the portion of the model state which is relevant
        // for checking that this action was processed correctly.
        partialState: cloneDeep(partialState),
      });
      if (checkProperties) {
        // Checking properties is flagged because it is computationally
        // expensive.

        // If a property does not hold, we write the trace to file for debugging
        // (and replaying).
        if (!validatorSetReplication(hist)) {
          dumpTrace(`${DIR}trace_${i}.json`, actions, events);
          throw 'validatorSetReplication property failure, trace written.';
        }
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
    // Only write trace if not checking properties because disk IO,
    // and we are not interested in the trace if the properties hold.
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
        `done ${i}, actions per second ${(i * NUM_ACTIONS) / (elapsedMillis / 1000)
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
 * 
 * The model is deterministic, thus a fixed list of actions always
 * results in the same behavior and model states.
 * 
 * @param actions
 */
function replayActions(actions: TraceAction[]) {
  const hist = new BlockHistory();
  const events: Event[] = [];
  const model = new Model(hist, events, MODEL_INIT_STATE);
  const actionGenerator = new ActionGenerator(model);
  for (let i = 0; i < actions.length; i++) {
    const a = actions[i];
    actionGenerator.do(a.action);
    doAction(model, a.action);
  }
}

/**
 * Takes a path to a json file containing traces and replays the trace
 * at the given index, for the given number of actions.
 * 
 * @param fn filename of the file containing the json traces
 * @param ix the index of the trace in the json
 * @param numActions The number of actions to replay from the trace. If numActions
 * is less than the length of the trace, then execution will complete before
 * the entire trace has been executed. This helps with debugging because it makes
 * logs shorter.
 */
function replayFile(fn: string, ix: number, numActions: number) {
  const traces = JSON.parse(fs.readFileSync(fn, 'utf8'));
  const trace = traces[ix];
  const traceActions = trace.actions as TraceAction[];
  const actions = traceActions.slice(0, numActions);
  replayActions(actions);
}

console.log(`running main`);

/*
 * Generate new traces and write them to files, for <seconds> seconds.
 *
 * Use a mixture of randomness and heuristics to generate random actions
 * and run them against the model. This is done many times, and the results
 * of each run are written to a file called a trace.
 *
 * yarn start gen <seconds>
 */
if (process.argv[2] === 'gen') {
  console.log(`gen`);
  console.log(`generating traces to /traces`);
  const seconds = parseInt(process.argv[3]);
  generateTraces(seconds, false);
} else if (process.argv[2] === 'properties') {
  /*
   * Check properties of the model for <seconds> seconds.
   *
   * The system has properties that must be true at all times. We
   * can check that the model satisfies these properties by running
   * random sequences of actions (as in the gen command) and checking
   * that after each action, the model is still in a state that satisfies
   * all the properties.
   *
   * yarn start properties <seconds>
   */
  console.log(`properties`);
  console.log(`checking that random executions satisfy properties`);
  const seconds = parseInt(process.argv[3]);
  generateTraces(seconds, true);
} else if (process.argv[2] === 'subset') {
  /*
   * Creates a trace file containing several traces, in a way that ensures
   * each interesting model event is emitted by some trace.
   * 
   * When generating millions of traces, many of them will be very similar
   * and you will not need all of them to get a good test coverage of your system.
   * It is useful to select a small subset of the traces, which can be run
   * efficiently and which cover all interesting events. 
   *
   * yarn start subset <output file abs path> <num event instances (optional)>
   * 
   * NOTE: num event instances = n means that the resulting subset of traces will
   * overall contain the event at least n times (if possible). If, over all traces,
   * the event occurs less than n times, then the subset will include all traces
   * including that event. WARNING: make sure that all events are covered!
   */
  console.log(`createSmallSubsetOfCoveringTraces`);
  console.log(`selecting a small subset of traces that cover all events`);
  const outFile = process.argv[3];

  let eventInstances = 400; // Sensible, conservative default. 

  if (3 < process.argv.length) {
    eventInstances = parseInt(process.argv[4]);
  }
  createSmallSubsetOfCoveringTraces(outFile, eventInstances);
} else if (process.argv[2] === 'replay') {
  /*
   * Replay a trace from a a file, up to a given number of actions.
   *
   * This is useful for debugging. If you have a failed test, you can 
   * step through the model and the SUT side-by-side using a debugger
   * or print statements.
   *
   * yarn start replay <filename> <list index> <num actions>
   */
  console.log(`replay`);
  console.log(`replaying the actions of a trace against a new model instance`);
  const [fn, traceNum, numActions] = process.argv.slice(3, 6);
  replayFile(fn, parseInt(traceNum), parseInt(numActions));
} else {
  console.log(`did not execute any function, please specify a function to run`);
}

console.log(`finished running main`);

export { generateTraces as gen };
