import * as fs from 'fs';
import timeSpan from 'time-span';
import { Blocks, Block } from './properties.js';
import {
  NUM_VALIDATORS,
  P,
  C,
  MAX_VALIDATORS,
  TOKEN_SCALAR,
  BLOCK_SECONDS,
  SLASH_DOUBLESIGN,
  SLASH_DOWNTIME,
} from './constants.js';
import _, { max } from 'underscore';
import { Model, Status } from './model.js';
import { Event } from './events.js';
import {
  stakingWithoutSlashing,
  bondBasedConsumerVotingPower,
} from './properties.js';
import { STATUS_CODES } from 'http';

function forceMakeEmptyDir(dir) {
  if (!fs.existsSync(dir)) {
    fs.mkdirSync(dir);
    return;
  }
  fs.rmSync(dir, { recursive: true });
  forceMakeEmptyDir(dir);
}

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
  jailed = new Array(NUM_VALIDATORS).fill(false);
  slashed = _.object([
    [P, new Map()],
    [C, new Map()],
  ]);

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
        JumpNBlocks: 0.45,
        Deliver: 0.45,
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
        const cntWouldBeNotJailed = this.jailed.filter(
          (j) => j !== i && !this.jailed[j],
        ).length;
        return MAX_VALIDATORS <= cntWouldBeNotJailed;
      })
      .map((i) => {
        return { kind: 'ProviderSlash', val: i };
      });
  };
  selectProviderSlash = (a): ProviderSlash => {
    this.jailed[a.val] = true;
    return {
      ...a,
      power: _.random(1, 6) * TOKEN_SCALAR,
      infractionHeight: Math.floor(Math.random() * this.model.h[C]),
      factor: _.sample([SLASH_DOUBLESIGN, SLASH_DOWNTIME]),
    };
  };

  candidateConsumerSlash = (): Action[] => {
    return _.range(NUM_VALIDATORS)
      .filter((i) => this.model.ccvC.power[i] !== undefined)
      .filter((i) => {
        const cntWouldBeNotJailed = this.jailed.filter(
          (j) => j !== i && !this.jailed[j],
        ).length;
        return MAX_VALIDATORS <= cntWouldBeNotJailed;
      })
      .map((i) => {
        return { kind: 'ConsumerSlash', val: i };
      });
  };
  selectConsumerSlash = (a): ConsumerSlash => {
    this.jailed[a.val] = true;
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
    if (this.model.t[P] === this.model.t[C]) {
      chainCandidates.push([P, C]);
    } else if (this.model.t[P] < this.model.t[C]) {
      chainCandidates.push([P]);
    } else {
      chainCandidates.push([C]);
    }
    a = {
      ...a,
      chains: _.sample(chainCandidates),
      n: _.sample([1, 6]),
      secondsPerBlock: BLOCK_SECONDS,
    };
    return a;
  };

  candidateDeliver = (): Action[] => {
    return [P, C]
      .filter((c) => this.model.hasUndelivered(c))
      .map((c) => {
        return { kind: 'Deliver', chain: c };
      });
  };
  selectDeliver = (a): Deliver => {
    return a;
  };
}

class Trace {
  actions = [];
  consequences = [];
  blocks = _.object([
    [P, new Map()],
    [C, new Map()],
  ]) as { provider: Map<number, Block>; consumer: Map<number, Block> };
  events = [];
  dump = (fn: string) => {
    const transitions = _.zip(this.actions, this.consequences).map(
      ([a, c]) => {
        return { action: a, consequence: c };
      },
    );
    const blocks = _.mapObject(this.blocks, (map) =>
      _.chain(Array.from(map.entries()))
        .pairs()
        .sortBy((pair) => pair[0]),
    );
    const json = JSON.stringify(
      { transitions, blocks, events: this.events },
      null,
      4,
    );
    fs.writeFileSync(fn, json);
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
    model.deliver(a.chain);
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

function writeEventData(allEvents, fn) {
  const eventCnt = _.countBy(allEvents, _.identity);
  for (const evt in Event) {
    const evtName = Event[evt];
    if (!_.has(eventCnt, evtName)) {
      eventCnt[evtName] = 0;
    }
  }
  const cnts = _.chain(eventCnt)
    .pairs()
    .sortBy((pair) => -pair[1]);

  fs.writeFileSync(`cnts${fn}.json`, JSON.stringify(cnts));
}

function gen() {
  const outerEnd = timeSpan();
  const GOAL_TIME_MINS = 5;
  const goalTimeMillis = GOAL_TIME_MINS * 60 * 1000;
  const NUM_ACTIONS = 40;
  const DIR = 'traces/';
  forceMakeEmptyDir(DIR);
  let numRuns = 1000000000000;
  let elapsedMillis = 0;
  let i = 0;
  const allEvents = [];
  while (i < numRuns) {
    i += 1;
    numRuns = Math.round(goalTimeMillis / (elapsedMillis / i) + 0.5);
    const end = timeSpan();
    ////////////////////////
    const blocks = new Blocks();
    const events = [];
    const model = new Model(blocks, events);
    const actionGenerator = new ActionGenerator(model);
    const trace = new Trace();
    for (let j = 0; j < NUM_ACTIONS; j++) {
      const a = actionGenerator.get();
      trace.actions.push(a);
      doAction(model, a);
      trace.consequences.push(model.snapshot());
    }
    let ok = true;
    ok = true;
    // ok = bondBasedConsumerVotingPower(blocks);
    if (!ok) {
      throw 'bondBasedConsumerVotingPower';
    }
    // ok = stakingWithoutSlashing(blocks);
    if (!ok) {
      throw 'stakingWithoutSlashing';
    }
    trace.dump(`${DIR}trace_${i}.json`);
    allEvents.push(...events);
    ////////////////////////
    elapsedMillis += end.rounded();
    if (i % 4000 === 0) {
      console.log(
        `done ${i}, traces per second ${i / (elapsedMillis / 1000)}`,
      );
    }
  }
  console.log(`ran ${Math.floor(outerEnd.seconds() / 60)} mins`);
  writeEventData(allEvents, 'Gen');
}

function replay(actions: Action[]) {
  const blocks = new Blocks();
  const events = [];
  const model = new Model(blocks, events);
  for (let i = 0; i < actions.length; i++) {
    const a = actions[i];
    doAction(model, a);
  }
}

function replayFile(fn: string) {
  const trace = JSON.parse(fs.readFileSync(fn, 'utf8'));
  replay(trace.transitions.map((t) => t.action));
}

console.log(`running  main`);
gen();
// replayFile('trace_bad.json');
console.log(`finished running main`);

export { gen };
