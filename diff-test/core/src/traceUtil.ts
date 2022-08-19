import * as fs from 'fs';
import * as childProcess from 'child_process';
import _ from 'underscore';
import { TraceAction, Chain, CommittedBlock, Event } from './common.js';

import {
  P,
  C,
  UNBONDING_SECONDS_P,
  UNBONDING_SECONDS_C,
  TRUSTING_SECONDS,
  NUM_VALIDATORS,
  MAX_VALIDATORS,
  JAIL_SECONDS,
  BLOCK_SECONDS,
  TOKEN_SCALAR,
  INITIAL_DELEGATOR_TOKENS,
  MAX_BLOCK_ADVANCES,
} from './constants.js';

/**
 * Record meta data to written traces.
 */
const meta = {
  // Commit of interchain-security/ that the trace was generated.
  commit: childProcess.execSync('git rev-parse HEAD').toString().trim(),
  // Diff between the working tree and the commit.
  diff: childProcess.execSync('git diff').toString().trim(),
};

/**
 * Forcibly ensure an empty directory exists.
 * @param dir directory name
 */
function forceMakeEmptyDir(dir: string) {
  if (!fs.existsSync(dir)) {
    fs.mkdirSync(dir);
    return;
  }
  fs.rmSync(dir, { recursive: true });
  forceMakeEmptyDir(dir);
}

/**
 * Write the trace data to file, with accompanying metadata.
 *
 * @param fn Filename
 * @param events Events included in trace
 * @param actions Actions included in trace
 * @param blocks Block snapshots included in trace
 */
function dumpTrace(
  fn: string,
  events: Event[],
  actions: TraceAction[],
  blocks: Record<Chain, Map<number, CommittedBlock>>,
) {
  const toDump = {
    // Record metadata
    meta,
    // Record values of model constants
    constants: {
      P,
      C,
      UNBONDING_SECONDS_P,
      UNBONDING_SECONDS_C,
      TRUSTING_SECONDS,
      NUM_VALIDATORS,
      MAX_VALIDATORS,
      JAIL_SECONDS,
      BLOCK_SECONDS,
      TOKEN_SCALAR,
      INITIAL_DELEGATOR_TOKENS,
      MAX_BLOCK_ADVANCES,
    },
    // Record which events occurred
    events,
    // Record which actions occured
    actions,
    // Record block snapshots, sorted by height and mapped by chain
    blocks: _.mapObject(blocks, (mapHtoSnapshot) =>
      _.sortBy(
        Array.from(mapHtoSnapshot.entries()),
        (pair) => pair[0],
      ).map((pair) => pair[1]),
    ),
  };
  // Write human readable JSON
  const json = JSON.stringify([toDump], null);
  fs.writeFileSync(fn, json);
}

/**
 * Reads all json traces in traces/ and creates a new trace file
 * consisting of a list of several traces. The traces in the new
 * trace file are chosen in such a way to ensure a covering of
 * each model event.
 * The traces are selected according to a greedy algorithm, ensuring
 * that each event occurs EVENT_INSTANCES times while somewhat
 * minimizing the number of traces included.
 * In this way, it is possible to obtain a concise set of traces which
 * test many model behaviors, reducing the time needed to test the SUT.
 *
 * @param outFile absolute filepath to write output to
 * @param numEventInstances max number of times to it each event
 */
function createSmallSubsetOfCoveringTraces(
  outFile: string,
  numEventInstances: number,
) {
  // directory to read traces from
  const DIR = 'traces/';
  // file to write the new traces to
  const inputFilenames: string[] = [];
  fs.readdirSync(DIR).forEach((file) => {
    inputFilenames.push(`${DIR}${file}`);
  });
  const maxPossibleCntForEvent: number[] = [];
  const cnt: number[] = [];
  // Maps event names to an index
  const ix: Record<string, number> = {};
  for (const evt in Event) {
    const i = Object.keys(Event).indexOf(evt);
    const stringRepr = Object.values(Event)[i];
    ix[stringRepr] = cnt.length;
    cnt.push(0);
    maxPossibleCntForEvent.push(0);
  }
  const eventCntsByTrace: [string, number[]][] = [];
  // For each trace file
  inputFilenames.forEach((fn) => {
    const trace = JSON.parse(fs.readFileSync(fn, 'utf8'))[0];
    const thisCnt: number[] = new Array(cnt.length).fill(0);
    // for each event that occurred in the trace
    trace.events.forEach((evtName: string) => {
      const i = ix[evtName];
      // cnt the occurrences in this trace
      thisCnt[i] += 1;
      // cnt the global occurrences
      maxPossibleCntForEvent[i] += 1;
    });
    eventCntsByTrace.push([fn, thisCnt]);
  });

  const targetCntForEvent = maxPossibleCntForEvent.map((x) =>
    Math.min(x, numEventInstances),
  );
  console.log(`finished reading traces and counting events`);

  /**
   * Computes greedy score for a event frequency cnt vector
   * @param v vector representing event counts
   * @returns
   */
  function score(v: number[]): number {
    let x = 0;
    for (let i = 0; i < v.length; i++) {
      // How many events of this type are still desired?
      const need = Math.max(targetCntForEvent[i] - cnt[i], 0);
      // How many events of this type does this trace have?
      const get = v[i];
      x += Math.min(need, get);
    }
    return x;
  }

  const outputFilenames: string[] = [];
  // While we have not reached the target occurrence count for all events
  while (cnt.some((x, i) => x < targetCntForEvent[i])) {
    // Sort by score descending
    eventCntsByTrace.sort((a, b) => score(b[1]) - score(a[1]));
    const [fn] = eventCntsByTrace.shift()!;
    // Use this trace
    outputFilenames.push(fn);
  }
  console.log(`num traces used: `, outputFilenames.length);
  const allTraces: any[] = [];
  outputFilenames.forEach((fn) => {
    const traceJson = JSON.parse(fs.readFileSync(fn, 'utf8'));
    const trace = traceJson[0];
    allTraces.push(trace);
  });
  fs.writeFileSync(outFile, JSON.stringify(allTraces));
}

/**
 * Pretty print the number of times each event occurs.
 * @param allEvents A map of event type to number of occurrences
 */
function logEventData(allEvents: Event[]) {
  const eventCnt = _.countBy(allEvents, _.identity);
  for (const evt in Event) {
    const evtName = (Event as any)[evt]; // TODO: remove hack
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
