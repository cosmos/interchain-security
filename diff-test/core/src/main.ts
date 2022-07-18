import * as fs from 'fs';
import _ from 'underscore';
import timeSpan from 'time-span';
import cloneDeep from 'clone-deep';
import { Blocks } from './properties.js';
import { Sanity } from './sanity.js';
import { Model, Status } from './model.js';
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
  SLASH_DOUBLESIGN,
  SLASH_DOWNTIME,
  BLOCK_SECONDS,
  TOKEN_SCALAR,
  MAX_JUMPS,
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
type ProviderSlash = {
  kind: string;
  val: number;
  power: number;
  infractionHeight: number;
  factor: number;
};
type ConsumerSlash = {
  kind: string;
  val: number;
  power: number;
  infractionHeight: number;
  isDowntime: number;
};

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

  get = () => {
    let templates: Action[] = _.flatten([
      this.candidateDelegate(),
      this.candidateUndelegate(),
      this.candidateJumpNBlocks(),
      this.candidateDeliver(),
      this.candidateProviderSlash(),
      this.candidateConsumerSlash(),
    ]);
    const possible = _.uniq(templates.map((a) => a.kind));
    const distr = _.pick(
      {
        Delegate: 0.03,
        Undelegate: 0.03,
        JumpNBlocks: 0.35,
        Deliver: 0.55,
        ProviderSlash: 0.02,
        ConsumerSlash: 0.02,
      },
      ...possible,
    );
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
    if (kind === 'ProviderSlash') {
      return this.selectProviderSlash(a);
    }
    if (kind === 'ConsumerSlash') {
      return this.selectConsumerSlash(a);
    }
    throw `kind doesn't match`;
  };

  candidateDelegate = (): Action[] => {
    return _.range(NUM_VALIDATORS).map((i) => {
      return {
        kind: 'Delegate',
        val: i,
      };
    });
  };
  selectDelegate = (a): Delegate => {
    return { ...a, amt: _.random(1, 5) * TOKEN_SCALAR };
  };

  candidateUndelegate = (): Action[] => {
    return _.range(NUM_VALIDATORS).map((i) => {
      return {
        kind: 'Undelegate',
        val: i,
      };
    });
  };
  selectUndelegate = (a): Undelegate => {
    return { ...a, amt: _.random(1, 4) * TOKEN_SCALAR };
  };

  candidateProviderSlash = (): Action[] => {
    return _.range(NUM_VALIDATORS)
      .filter((i) => this.model.staking.status[i] !== Status.UNBONDED)
      .filter((i) => {
        const cntWouldBeNotJailed = this.didSlash.filter(
          (slashed, j) => !slashed && j !== i,
        ).length;
        return 1 <= cntWouldBeNotJailed;
      })
      .map((i) => {
        return { kind: 'ProviderSlash', val: i };
      });
  };
  selectProviderSlash = (a): ProviderSlash => {
    this.didSlash[a.val] = true;
    return {
      ...a,
      power: _.random(1, 6) * TOKEN_SCALAR,
      infractionHeight: Math.floor(Math.random() * this.model.h[P]),
      factor: _.sample([SLASH_DOUBLESIGN, SLASH_DOWNTIME]),
    };
  };

  candidateConsumerSlash = (): Action[] => {
    return (
      _.range(NUM_VALIDATORS)
        // TODO: can I remove this filter?
        .filter((i) => this.model.ccvC.power[i] !== undefined)
        .filter((i) => {
          const cntWouldBeNotJailed = this.didSlash.filter(
            (slashed, j) => !slashed && j !== i,
          ).length;
          return 1 <= cntWouldBeNotJailed;
        })
        .map((i) => {
          return { kind: 'ConsumerSlash', val: i };
        })
    );
  };
  selectConsumerSlash = (a): ConsumerSlash => {
    this.didSlash[a.val] = true;
    return {
      ...a,
      power: _.random(1, 6) * TOKEN_SCALAR,
      infractionHeight: Math.floor(Math.random() * this.model.h[C]),
      isDowntime: _.sample([true, false]),
    };
  };

  candidateJumpNBlocks = (): Action[] => [{ kind: 'JumpNBlocks' }];
  selectJumpNBlocks = (a): JumpNBlocks => {
    const chainCandidates = [];
    // TODO: need to decide where this tLastCommit ect data lives
    if (
      this.model.sanity.tLastCommit[P] ===
      this.model.sanity.tLastCommit[C]
    ) {
      chainCandidates.push([P, C]);
    } else if (
      this.model.sanity.tLastCommit[P] < this.model.sanity.tLastCommit[C]
    ) {
      chainCandidates.push([P]);
    } else {
      chainCandidates.push([C]);
    }
    a = {
      ...a,
      chains: _.sample(chainCandidates),
      n: _.sample([1, MAX_JUMPS]),
      secondsPerBlock: BLOCK_SECONDS,
    };
    return a;
  };

  candidateDeliver = (): Action[] => {
    return [P, C]
      .filter((c) => 0 < this.model.outbox[c == P ? C : P].numAvailable())
      .map((c) => {
        return {
          kind: 'Deliver',
          chain: c,
        };
      });
  };
  selectDeliver = (a): Deliver => {
    a = {
      ...a,
      numPackets: _.random(
        1,
        this.model.outbox[a.chain == P ? C : P].numAvailable(),
      ),
    };
    return a;
  };
}

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
  if (kind === 'ProviderSlash') {
    const a = action as ProviderSlash;
    model.providerSlash(a.val, a.infractionHeight, a.power, a.factor);
  }
  if (kind === 'ConsumerSlash') {
    const a = action as ConsumerSlash;
    model.consumerSlash(a.val, a.power, a.infractionHeight, a.isDowntime);
  }
}

function gen(minutes) {
  const goalTimeMillis = minutes * 60 * 1000;
  let elapsedMillis = 0;
  const NUM_ACTIONS = 120;
  const DIR = 'tracesWithSlashing/';
  forceMakeEmptyDir(DIR);
  let i = 0;
  const allEvents = [];
  while (elapsedMillis < goalTimeMillis) {
    i += 1;
    const end = timeSpan();
    ////////////////////////
    const sanity = new Sanity();
    const blocks = new Blocks();
    const events = [];
    const model = new Model(sanity, blocks, events);
    const actionGenerator = new ActionGenerator(model);
    const actions = [];
    for (let j = 0; j < NUM_ACTIONS; j++) {
      const a = actionGenerator.get();
      doAction(model, a);
      actions.push({
        action: a,
        hLastCommit: cloneDeep(blocks.hLastCommit),
      });
    }
    dumpTrace(`${DIR}trace_${i}.json`, events, actions, blocks.blocks);
    allEvents.push(...events);
    ////////////////////////
    elapsedMillis += end.rounded();
    if (i % 2000 === 0) {
      console.log(
        `done ${i}, actions per second ${
          (i * NUM_ACTIONS) / (elapsedMillis / 1000)
        }`,
      );
    }
  }
  logEventData(allEvents);
}

function replay(actions: Action[]) {
  const sanity = new Sanity();
  const blocks = new Blocks();
  const events = [];
  const model = new Model(sanity, blocks, events);
  for (let i = 0; i < actions.length; i++) {
    const a = actions[i];
    doAction(model, a);
  }
}

function replayFile(fn: string, ix: number, numActions: number) {
  const traces = JSON.parse(fs.readFileSync(fn, 'utf8'));
  const trace = ix !== undefined ? traces[ix] : traces[0];
  const actions = trace.actions.map((a) => a.action).slice(0, numActions);
  replay(actions);
}

console.log(`running main`);

// yarn start gen <minutes>
if (process.argv[2] === 'gen') {
  console.log(`gen`);
  const minutes = parseInt(process.argv[3]);
  gen(minutes);
} // yarn start subset
else if (process.argv[2] === 'subset') {
  console.log(`createSmallSubsetOfCoveringTraces`);
  createSmallSubsetOfCoveringTraces();
} // yarn start replay <filename> <list index> <num actions>
else if (process.argv[2] === 'replay') {
  console.log(`replay`);
  const [fn, traceNum, numActions] = process.argv.slice(3, 6);
  replayFile(fn, parseInt(traceNum), parseInt(numActions));
} else {
  console.log(`did not execute any function`);
}

console.log(`finished running main`);

export { gen };
