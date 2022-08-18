import * as fs from 'fs';
import _ from 'underscore';
import timeSpan from 'time-span';
import cloneDeep from 'clone-deep';
import {
  BlockHistory
} from './properties.js';
import { Sanity as SanityChecker } from './sanity.js';
import { Model } from './model.js';
import {
  createSmallSubsetOfCoveringTraces,
  dumpTrace,
  forceMakeEmptyDir,
  logEventData,
} from './util.js';
import {
  P,
  C,
  NUM_VALIDATORS,
  BLOCK_SECONDS,
  TOKEN_SCALAR,
  MAX_BLOCK_ADVANCES,
} from './constants.js';

interface Action {
  kind: string;
}

type Delegate = {
  kind: string;
  val: number;
  amt: number;
};

type Undelegate = {
  kind: string;
  val: number;
  amt: number;
};

type JumpNBlocks = {
  kind: string;
  chains: string[];
  n: number;
  secondsPerBlock: number;
};

type Deliver = {
  kind: string;
  chain: string;
  numPackets: string;
};

type ConsumerSlash = {
  kind: string;
  val: number;
  infractionHeight: number;
  isDowntime: number;
};

/**
 * Takes an object where values are probabilities and returns a random
 * key based on the distribution.
 */
function weightedRandomKey(distr) {
  const scalar = _.reduce(_.values(distr), (sum, y) => sum + y, 0);
  const x = Math.random() * scalar;
  const pairs = _.pairs(distr);
  let i = 0;
  let cum = 0;
  while (i < pairs.length - 1 && cum + pairs[i][1] < x) {
    cum += pairs[i][1];
    i += 1;
  }
  return pairs[i][0];
}

class ActionGenerator {
  model;
  didSlash = new Array(NUM_VALIDATORS).fill(false);

  constructor(model) {
    this.model = model;
  }

  /**
   * Get a new model action.
   * An action is chosen by a process of generating and then selecting
   * template actions based on the current state of the model.
   * In this way, only actions which make sense given the current state
   * of the model can be returned. Among the possible actions, one is
   * chosen based on a probability distribution.
   * @returns An executable model action
   */
  get = () => {
    // Get candidate actions
    let templates: Action[] = _.flatten([
      this.candidateDelegate(),
      this.candidateUndelegate(),
      this.candidateJumpNBlocks(),
      this.candidateDeliver(),
      this.candidateConsumerSlash(),
    ]);
    // Get the names of each possible action
    const possibleActions = _.uniq(templates.map((a) => a.kind));
    // Build a probability distribution for each possible action
    const distr = _.pick(
      {
        Delegate: 0.03,
        Undelegate: 0.03,
        JumpNBlocks: 0.37,
        Deliver: 0.55,
        ConsumerSlash: 0.02,
      },
      ...possibleActions,
    );
    // Choose an action type (kind) based on the probability distribution
    const kind = weightedRandomKey(distr);
    templates = templates.filter((a) => a.kind === kind);
    const a = _.sample(templates);
    if (kind === 'Delegate') {
      return this.selectDelegate(a);
    }
    if (kind === 'Undelegate') {
      return this.selectUndelegate(a);
    }
    if (kind === 'JumpNBlocks') {
      return this.selectJumpNBlocks(a);
    }
    if (kind === 'Deliver') {
      return this.selectDeliver(a);
    }
    if (kind === 'ConsumerSlash') {
      return this.selectConsumerSlash(a);
    }
    throw `kind doesn't match`;
  };

  // Return templates for possible delegate actions
  candidateDelegate = (): Action[] => {
    return _.range(NUM_VALIDATORS).map((i) => {
      return {
        kind: 'Delegate',
        val: i,
      };
    });
  };

  // Fill out template for a selected Delegate action
  selectDelegate = (a): Delegate => {
    return { ...a, amt: _.random(1, 5) * TOKEN_SCALAR };
  };

  // Return templates for possible undelegate actions
  candidateUndelegate = (): Action[] => {
    return _.range(NUM_VALIDATORS).map((i) => {
      return {
        kind: 'Undelegate',
        val: i,
      };
    });
  };

  // Fill out template for a selected Undelegate action
  selectUndelegate = (a): Undelegate => {
    return { ...a, amt: _.random(1, 4) * TOKEN_SCALAR };
  };

  // Return templates for possible Consumer initiated slash actions
  candidateConsumerSlash = (): Action[] => {
    return _.range(NUM_VALIDATORS)
      // Filter out absent validators
      .filter((i) => this.model.ccvC.power[i] !== undefined)
      // Filter out validators if slashing that validator would
      // lead to all validators being jailed.
      .filter((i) => {
        const cntWouldBeNotJailed = this.didSlash.filter(
          (slashed, j) => !slashed && j !== i,
        ).length;
        return 1 <= cntWouldBeNotJailed;
      })
      .map((i) => {
        return { kind: 'ConsumerSlash', val: i };
      });
  };

  // Fill out a template for a selected Consumer initiated slash action
  selectConsumerSlash = (a): ConsumerSlash => {
    this.didSlash[a.val] = true;
    return {
      ...a,
      infractionHeight: Math.floor(Math.random() * this.model.h[C]),
      isDowntime: _.sample([true, false]),
    };
  };

  // Return templates for possible JumpNBlocks actions
  candidateJumpNBlocks = (): Action[] => [{ kind: 'JumpNBlocks' }];

  // Fill out a template for a selected JumpNBlocks action
  selectJumpNBlocks = (a): JumpNBlocks => {
    // A JumpNBlocks action must be chosen to not advance either
    // chain too far ahead so that the IBC clients would expire as a result.
    const chainCandidates = [];
    if (
      this.model.sanity.tLastCommit[P] ===
      this.model.sanity.tLastCommit[C]
    ) {
      // In case that both chains share the same last commit timestamp
      // either chain can be advanced.
      chainCandidates.push([P, C]);
    }
    // Else, choose the chain that advanced furthest in the past.
    else if (
      this.model.sanity.tLastCommit[P] < this.model.sanity.tLastCommit[C]
    ) {
      chainCandidates.push([P]);
    } else {
      chainCandidates.push([C]);
    }
    a = {
      ...a,
      chains: _.sample(chainCandidates),
      // Choose the number of blocks from {1, MAX_JUMP}
      n: _.sample([1, MAX_BLOCK_ADVANCES]),
      secondsPerBlock: BLOCK_SECONDS,
    };
    return a;
  };

  // Return templates for possible packet Deliver actions
  candidateDeliver = (): Action[] => {
    return [P, C]
      // Only choose a candidate chain if there are deliverable packets available
      // in the network.
      .filter((c) => 0 < this.model.outbox[c == P ? C : P].numAvailable())
      .map((c) => {
        return {
          kind: 'Deliver',
          chain: c,
        };
      });
  };

  // Fill out a selected Deliver action template
  selectDeliver = (a): Deliver => {
    a = {
      ...a,
      // Randomly choose to deliver 1 or more packets
      numPackets: _.random(
        1,
        this.model.outbox[a.chain == P ? C : P].numAvailable(),
      ),
    };
    return a;
  };
}

/**
 * Executes an action against the model, thereby updating the model state.
 * @param model The model instance
 * @param action The action to be executed against the model
 */
function doAction(model, action: Action) {
  const kind = action.kind;
  if (kind === 'Delegate') {
    const a = action as Delegate;
    model.delegate(a.val, a.amt);
  }
  if (kind === 'Undelegate') {
    const a = action as Undelegate;
    model.undelegate(a.val, a.amt);
  }
  if (kind === 'JumpNBlocks') {
    const a = action as JumpNBlocks;
    model.jumpNBlocks(a.n, a.chains, a.secondsPerBlock);
  }
  if (kind === 'Deliver') {
    const a = action as Deliver;
    model.deliver(a.chain, a.numPackets);
  }
  if (kind === 'ConsumerSlash') {
    const a = action as ConsumerSlash;
    model.consumerSlash(a.val, a.infractionHeight, a.isDowntime);
  }
}

/**
 * Generates traces by repeatedly creating new model instances
 * and executing randomly generated actions against them.
 * The trace consists of data including the actions taken, and the
 * successive model states that result from the actions. Additional
 * data is included
 * @param minutes The number of minutes to generate traces.
 */
function gen(minutes) {
  // Compute millis run time
  const runTimeMillis = minutes * 60 * 1000;
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
    const sanity = new SanityChecker();
    const blocks = new BlockHistory();
    // Store all events emitted during trace execution
    const events = [];
    const model = new Model(sanity, blocks, events);
    const actionGenerator = new ActionGenerator(model);
    const actions = [];
    for (let j = 0; j < NUM_ACTIONS; j++) {
      const a = actionGenerator.get();
      doAction(model, a);
      actions.push({
        // Store the action taken
        action: a,
        // Store a snapshot of the model state at the given block commit
        // this is used for model comparisons when testing the SUT.
        hLastCommit: cloneDeep(blocks.hLastCommit),
      });
    }
    // Write the trace to file, along with metadata.
    dumpTrace(`${DIR}trace_${i}.json`, events, actions, blocks.blocks);
    // Accumulate all events
    allEvents.push(...events);
    ////////////////////////
    elapsedMillis += end.rounded();
    // Log progress stats
    if (i % 2000 === 0) {
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
 * The model is deterministic, thus a fixed list of actions always
 * results in the same behavior and model states.
 * @param actions 
 */
function replay(actions: Action[]) {
  const sanity = new SanityChecker();
  const blocks = new BlockHistory();
  const events = [];
  const model = new Model(sanity, blocks, events);
  for (let i = 0; i < actions.length; i++) {
    const a = actions[i];
    doAction(model, a);
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
  const actions = trace.actions.map((a) => a.action).slice(0, numActions);
  replay(actions);
}

console.log(`running main`);

/*
 * Generate new traces and write them to files, for <minutes> minutes.
 *
 * yarn start gen <minutes> 
 */
if (process.argv[2] === 'gen') {
  console.log(`gen`);
  const minutes = parseInt(process.argv[3]);
  gen(minutes);
}
/*
 * Creates a trace file containing several traces, in a way that ensures
 * each interesting model event is emitted by some trace.
 * 
 * yarn start subset
 */
else if (process.argv[2] === 'subset') {
  console.log(`createSmallSubsetOfCoveringTraces`);
  createSmallSubsetOfCoveringTraces();
}
/*
 * Replay a trace from a a file, up to a given number of actions.
 * 
 * yarn start replay <filename> <list index> <num actions>
 */
else if (process.argv[2] === 'replay') {
  console.log(`replay`);
  const [fn, traceNum, numActions] = process.argv.slice(3, 6);
  replayFile(fn, parseInt(traceNum), parseInt(numActions));
} else {
  console.log(`did not execute any function`);
}

console.log(`finished running main`);

export { gen };
