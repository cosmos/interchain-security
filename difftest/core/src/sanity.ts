import { P, C, TRUSTING_SECONDS } from './constants.js';
import { Chain, Validator } from './common.js';

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
  tLastTrustedHeader = { provider: 0, consumer: 0 };
  // the timestamp of the last committed block
  tLastCommit = { provider: 0, consumer: 0 };

  /**
   * Records the updating of a client on chain at time t
   */
  updateClient = (chain: Chain, t: number) => {
    if (this.tLastTrustedHeader[chain] + TRUSTING_SECONDS <= t) {
      throw 'EXPIRED! - not supposed to happen. There is a mistake in how the model or generator is written.';
    }
    this.tLastTrustedHeader[chain] = this.tLastCommit[chain == P ? C : P];
  };

  /**
   * Records the commitment of a block on chain at time t
   */
  commitBlock = (chain: Chain, t: number) => {
    this.tLastCommit[chain] = t;
  };

  /**
   * Checks that a new validator set is sensible.
   */
  newValSet = (vals: Validator[]) => {
    if (vals.length < 1) {
      throw 'EMPTY VAL SET! - not supposed to happen. There is a mistake in how the model or generator is written.';
    }
  };
}

export { Sanity };
