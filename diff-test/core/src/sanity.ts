import _ from 'underscore';
import { P, C, TRUSTING_SECONDS } from './constants.js';

/**
 * Checks that the model does not overapproximate the system
 * too much, as this would make it less useful for generating tests.
 *
 * For example, we should not ever
 *    - allow an empty validator set
 *    - cause a tendermint light client to expire
 */
class Sanity {
  // the timestamp contained in the latest trusted header
  tLastTrustedHeader = _.object([
    [P, 0],
    [C, 0],
  ]) as { provider: number; consumer: number };
  // the timestamp of the last committed block
  tLastCommit = _.object([
    [P, 0],
    [C, 0],
  ]);

  updateClient = (chain, t) => {
    if (this.tLastTrustedHeader[chain] + TRUSTING_SECONDS <= t) {
      throw 'EXPIRED! - not supposed to happen. There is a mistake in how the model or generator is written.';
    }
    this.tLastTrustedHeader[chain] = this.tLastCommit[chain == P ? C : P];
  };
  commitBlock = (chain, t) => {
    this.tLastCommit[chain] = t;
  };
  newValSet = (vals) => {
    if (vals.len < 1) {
      throw 'EMPTY VAL SET! - not supposed to happen. There is a mistake in how the model or generator is written.';
    }
  };
}

export { Sanity };
