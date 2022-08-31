import * as fs from 'fs';
import * as childProcess from 'child_process';
import _ from 'underscore';
import { TraceAction } from './common.js';
import { Event } from './constants.js';

import {
  P,
  C,
  UNBONDING_SECONDS_P,
  UNBONDING_SECONDS_C,
  TRUSTING_SECONDS,
  NUM_VALIDATORS,
  MAX_VALIDATORS,
  SLASH_DOUBLESIGN,
  SLASH_DOWNTIME,
  JAIL_SECONDS,
  BLOCK_SECONDS,
  INITIAL_DELEGATOR_TOKENS,
  DELEGATE_AMT_MIN,
  DELEGATE_AMT_MAX,
  UNDELEGATE_AMT_MIN,
  UNDELEGATE_AMT_MAX,
  ISDOWNTIME_PROBABILITY,
  MAX_NUM_PACKETS_FOR_DELIVER,
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
function dumpTrace(fn: string, actions: TraceAction[], events: Event[]) {
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
      SLASH_DOUBLESIGN,
      SLASH_DOWNTIME,
      JAIL_SECONDS,
      BLOCK_SECONDS,
      INITIAL_DELEGATOR_TOKENS,
      DELEGATE_AMT_MIN,
      DELEGATE_AMT_MAX,
      UNDELEGATE_AMT_MIN,
      UNDELEGATE_AMT_MAX,
      ISDOWNTIME_PROBABILITY,
      MAX_NUM_PACKETS_FOR_DELIVER,
    },
    // Record which actions occurred
    actions,
    // Events which occurred
    events,
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
 * @param outFilePrefix absolute filepath to write output to
 * @param targetCntForEventMax max number of times to it each event
 */
function createSmallSubsetOfCoveringTraces(
  outFilePrefix: string,
  targetCntForEventMax: number,
) {
  // directory to read traces from
  const DIR = 'traces/';
  // file to write the new traces to
  const inputFilenames: string[] = [];

  fs.readdirSync(DIR).forEach((fn) => {
    inputFilenames.push(`${DIR}${fn}`);
  });

  const eventNameToCounterIx: Record<string, number> = {};

  for (const evt in Event) {
    const stringRepr = Event[evt as keyof typeof Event];
    eventNameToCounterIx[stringRepr] = Object.keys(Event).indexOf(evt);
  }

  const NUM_EVENTS = Object.keys(Event).length;

  const maxPossibleCntForEvent = new Array(NUM_EVENTS).fill(0);

  const eventCntsByTrace: [string, number[]][] = [];
  // For each trace file
  inputFilenames.forEach((fn) => {
    const trace = JSON.parse(fs.readFileSync(fn, 'utf8'))[0];
    const traceEventCnt: number[] = new Array(
      Object.keys(Event).length,
    ).fill(0);
    // for each event that occurred in the trace
    trace.events.forEach((evtName: string) => {
      const i = eventNameToCounterIx[evtName];
      // cnt the occurrences in this trace
      traceEventCnt[i] += 1;
      // cnt the global occurrences
      maxPossibleCntForEvent[i] += 1;
    });
    eventCntsByTrace.push([fn, traceEventCnt]);
  });

  const targetCntForEvent = maxPossibleCntForEvent.map((x) =>
    Math.min(x, targetCntForEventMax),
  );

  const accumulatedCntForEvent = new Array(NUM_EVENTS).fill(0);
  /**
   * Computes greedy score for a event frequency cnt vector
   * @param v vector representing event counts
   * @returns
   */
  function score(v: number[]): number {
    let x = 0;
    for (let i = 0; i < v.length; i++) {
      // How many events of this type are still desired?
      const need = Math.max(
        targetCntForEvent[i] - accumulatedCntForEvent[i],
        0,
      );
      // How many events of this type does this trace have?
      const get = v[i];
      x += Math.min(need, get);
    }
    return x;
  }

  const outputFilenames: string[] = [];
  // While we have not reached the target occurrence count for all events
  while (
    accumulatedCntForEvent.some((x, i) => x < targetCntForEvent[i])
  ) {
    // Sort by score descending
    eventCntsByTrace.sort((a, b) => score(b[1]) - score(a[1]));
    const [fn, traceEventCnt] = eventCntsByTrace.shift()!;
    for (let i = 0; i < traceEventCnt.length; i++) {
      accumulatedCntForEvent[i] += traceEventCnt[i];
    }
    // Use this trace
    outputFilenames.push(fn);
  }

  // Diagnostic ////////////////////////////////////////////
  console.log(`num traces used: `, outputFilenames.length);
  for (let i = 0; i < accumulatedCntForEvent.length; i++) {
    const evtName = Object.keys(Event)[i];
    const cnt = accumulatedCntForEvent[i];
    console.log(evtName, cnt);
  }
  //////////////////////////////////////////////////////////

  const allTraces: any[] = [];
  outputFilenames.forEach((fn) => {
    const traceJson = JSON.parse(fs.readFileSync(fn, 'utf8'));
    const trace = traceJson[0];
    allTraces.push(trace);
  });
  fs.writeFileSync(outFilePrefix, JSON.stringify(allTraces));
}

/**
 * Pretty print the number of times each event occurs.
 * @param allEvents A map of event type to number of occurrences
 */
function logEventData(allEvents: Event[]) {
  const eventCnt = _.countBy(allEvents, _.identity);
  for (const evt in Event) {
    const evtName = (Event as any)[evt];
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
