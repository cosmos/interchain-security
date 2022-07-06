import * as fs from 'fs';
import _ from 'underscore';
import { Event } from './events.js';

function createSmallSubsetOfCoveringTraces() {
  const DIR = 'traces/';
  let fns = [];
  fs.readdirSync(DIR).forEach((file) => {
    fns.push(`${DIR}${file}`);
  });
  const cnt = [];
  const ix = {};
  for (const evt in Event) {
    ix[Event[evt]] = cnt.length;
    cnt.push(0);
  }
  const hits = [];
  fns.forEach((fn) => {
    const trace = JSON.parse(fs.readFileSync(fn, 'utf8'));
    const hit = [fn, _.clone(cnt)];
    trace.events.forEach((evtName) => {
      hit[1][ix[evtName]] += 1;
    });
    hits.push(hit);
  });
  console.log(`finished reading files and cnting`);
  const TARGET = 100;
  function score(v): number {
    let x = 0;
    for (let i = 0; i < v.length; i++) {
      const need = Math.max(TARGET - cnt[i], 0);
      const get = v[i];
      x += Math.min(need, get);
    }
    return x;
  }
  fns = [];
  while (_.some(cnt, (x) => x < TARGET)) {
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

export { createSmallSubsetOfCoveringTraces };
