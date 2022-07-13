import * as fs from 'fs';
import _ from 'underscore';
import { Event } from './events.js';

function createSmallSubsetOfCoveringTraces() {
  const DIR = 'traces/';
  let fns = [];
  fs.readdirSync(DIR).forEach((file) => {
    fns.push(`${DIR}${file}`);
  });
  // fns = fns.slice(0, 1000);
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
  const target = possible.map((x) => Math.min(x, 1500));
  console.log(`finished reading files and cnting`);
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

export { createSmallSubsetOfCoveringTraces };
