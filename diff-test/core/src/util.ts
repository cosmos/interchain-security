import * as fs from 'fs';
import * as childProcess from 'child_process';
import _ from 'underscore';
import { Event } from './events.js';

import {
  P,
  C,
  UNBONDING_SECONDS_P,
  UNBONDING_SECONDS_C,
  TRUSTING_SECONDS,
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
  MAX_JUMPS,
} from './constants.js';

const meta = {
  commit: childProcess.execSync('git rev-parse HEAD').toString().trim(),
  diff: childProcess.execSync('git diff').toString().trim(),
};

function forceMakeEmptyDir(dir) {
  if (!fs.existsSync(dir)) {
    fs.mkdirSync(dir);
    return;
  }
  fs.rmSync(dir, { recursive: true });
  forceMakeEmptyDir(dir);
}

function dumpTrace(fn: string, events, actions, blocks) {
  const toDump = {
    meta,
    constants: {
      P,
      C,
      UNBONDING_SECONDS_P,
      UNBONDING_SECONDS_C,
      TRUSTING_SECONDS,
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
      MAX_JUMPS,
    },
    events,
    actions,
    blocks: _.mapObject(blocks, (mapHtoSnapshot) =>
      _.sortBy(
        Array.from(mapHtoSnapshot.entries()),
        (pair) => pair[0],
      ).map((pair) => pair[1]),
    ),
  };
  const json = JSON.stringify(toDump, null, 4);
  fs.writeFileSync(fn, json);
}

function createSmallSubsetOfCoveringTraces() {
  const DIR = 'traces/';
  let fns = [];
  fs.readdirSync(DIR).forEach((file) => {
    fns.push(`${DIR}${file}`);
  });
  const possible = [];
  const cnt = [];
  const ix = {};
  for (const evt in Event) {
    ix[Event[evt]] = cnt.length;
    cnt.push(0);
    possible.push(0);
  }
  const hits = [];
  fns.forEach((fn) => {
    const trace = JSON.parse(fs.readFileSync(fn, 'utf8'));
    const hit = [fn, _.clone(cnt)];
    trace.events.forEach((evtName) => {
      hit[1][ix[evtName]] += 1;
      possible[ix[evtName]] += 1;
    });
    hits.push(hit);
  });
  const target = possible.map((x) => Math.min(x, 250));
  console.log(`finished reading traces and counting events`);
  function score(v): number {
    let x = 0;
    for (let i = 0; i < v.length; i++) {
      const need = Math.max(target[i] - cnt[i], 0);
      const get = v[i];
      x += Math.min(need, get);
    }
    return x;
  }
  fns = [];
  while (_.some(cnt, (x, i) => x < target[i])) {
    hits.sort((a, b) => score(b[1]) - score(a[1]));
    const [fn, v] = hits.shift();
    fns.push(fn);
    for (let i = 0; i < v.length; i++) {
      cnt[i] += v[i];
    }
  }
  for (const evt in Event) {
    console.log(Event[evt], cnt[ix[Event[evt]]]);
  }
  console.log(`num traces: `, fns.length);
  const allTraces = [];
  fns.forEach((fn) => {
    allTraces.push(JSON.parse(fs.readFileSync(fn, 'utf8')));
  });
  fs.writeFileSync(`covering.json`, JSON.stringify(allTraces));
}

function logEventData(allEvents) {
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

  console.log(cnts);
}

export {
  createSmallSubsetOfCoveringTraces,
  dumpTrace,
  forceMakeEmptyDir,
  logEventData,
};
