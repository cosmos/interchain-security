import { strict as assert } from 'node:assert';
import _ from 'underscore';
import {
  P,
  C,
  UNBONDING_SECONDS_C,
  NUM_VALIDATORS,
} from './constants.js';
import { Chain, Validator, Snapshot } from './model.js'

/**
 * Data structure used to store a partial order of blocks. The partial order
 * is induced by packet delivery for blocks on different chains, and by height
 * for blocks on the same chain.
 * See https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/system_model_and_properties.md#system-properties
 */
class PartialOrder {
  // map chain -> block height in chain -> block height in counterparty chain
  greatestPred: Record<Chain, Map<number, number>> = { provider: new Map(), consumer: new Map() }
  // map chain -> block height in chain -> block height in counterparty chain
  leastSucc: Record<Chain, Map<number, number>> = { provider: new Map(), consumer: new Map() }

  /**
   * Mark the delivery of a packet. Induces a partial order between blocks
   * on different chains.
   * @param receivingChain chain receiving packet
   * @param sendHeight send height on sending chain
   * @param receiveHeight receive height on receiving chain
   */
  deliver = (receivingChain: Chain, sendHeight: number, receiveHeight: number) => {
    // TODO: can refactor to use if statement instead of typecast
    let h = sendHeight;
    if (this.greatestPred[receivingChain].has(receiveHeight)) {
      h = Math.max(
        this.greatestPred[receivingChain].get(receiveHeight)!,
        h,
      );
    }
    this.greatestPred[receivingChain].set(receiveHeight, h);
    const sendingChain = receivingChain === P ? C : P;
    h = receiveHeight;
    if (this.leastSucc[sendingChain].has(sendHeight)) {
      h = Math.min(this.leastSucc[sendingChain].get(sendHeight)!, h);
    }
    this.leastSucc[sendingChain].set(sendHeight, h);
  };

  /**
   * @param chain chain of block
   * @param height height of block
   * @returns Returns the height greatest predecessing block on the counterparty
   * chain if it exists, else undefined.
   */
  getGreatestPred = (chain: Chain, height: number) => {
    const it = this.greatestPred[chain].keys();
    let bestH = -1;
    let bestV = -1;
    let result = it.next();
    while (!result.done) {
      const h = result.value;
      if (bestH < h && h <= height) {
        bestH = h;
        bestV = this.greatestPred[chain].get(h)!;
      }
      result = it.next();
    }
    if (bestV === -1) {
      return undefined;
    }
    return bestV;
  };

  /**
   * 
   * @param chain chain of block
   * @param height height of block
   * @returns Returns the height of the least successing block on the counterparty
   * chain if it exists, else undefined.
   */
  getLeastSucc = (chain: Chain, height: number) => {
    const it = this.leastSucc[chain].keys();
    let bestH = 100000000000000; // Infinity
    let bestV = -1;
    let result = it.next();
    while (!result.done) {
      const h = result.value;
      if (h < bestH && height <= h) {
        bestH = h;
        bestV = this.leastSucc[chain].get(h)!;
      }
      result = it.next();
    }
    if (bestV === -1) {
      return undefined;
    }
    return bestV;
  };
}

/**
 * Store a snapshot of the model state for a given block height and time.
 */
interface Block {
  h: number;
  t: number;
  snapshot: Snapshot;
}

class BlockHistory {
  partialOrder = new PartialOrder();
  blocks = _.object([
    [P, new Map()],
    [C, new Map()],
  ]) as { provider: Map<number, Block>; consumer: Map<number, Block> };
  hLastCommit = _.object([
    [P, 0],
    [C, 0],
  ]) as { provider: number; consumer: number };
  commitBlock = (chain: Chain, snapshot: Snapshot) => {
    const h = snapshot.h[chain];
    const t = snapshot.t[chain];
    const b: Block = {
      h,
      t,
      snapshot,
    };
    this.blocks[chain].set(h, b);
    this.hLastCommit[chain] = h;
  };
}

function sum(arr: number[]): number {
  return arr.reduce((accum: number, x: number) => accum + x, 0)
}

/**
 * Is the total fund value in the system constant?
 * It only makes sense to check this if slashing with non-zero
 * slash factors never occurs, because slashing with non-zero
 * slash factors burns funds.
 * 
 * @param hist A history of blocks.
 * @returns Is the property satisfied?
 */
function stakingWithoutSlashing(hist: BlockHistory): boolean {
  const blocks = _.sortBy(
    Array.from(hist.blocks[P].entries()),
    (e) => e[0],
  )
    .map((e) => e[1])
    .map((b) => b.snapshot);
  if (blocks.length < 2) {
    return true;
  }

  function value(b) {
    let x = b.delegatorTokens;
    x += sum(b.tokens);
    x += sum(b.undelegationQ.map((e) => e.balance));
    return x;
  }

  const v = value(blocks[0]);
  for (let i = 1; i < blocks.length; i++) {
    if (value(blocks[i]) !== v) {
      return false;
    }
  }
  return true;
}

/**
 * Checks the bond-based consumer voting power property as defined
 * in https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/system_model_and_properties.md#system-properties
 * but modified to account for finite executions and always zero slash factors.
 * 
 * @param hist A history of blocks.
 * @returns Is the property satisfied?
 */
function bondBasedConsumerVotingPower(hist: BlockHistory): boolean {
  const partialOrder = hist.partialOrder;
  const blocks = hist.blocks;
  function powerProvider(block) {
    return _.range(NUM_VALIDATORS).map(
      (i) =>
        block.snapshot.tokens[i] +
        sum(
          block.snapshot.undelegationQ
            .filter((e) => e.val === i)
            .map((e) => e.initialBalance),
        ),
    );
  }
  function powerConsumer(block: Block) {
    return block.snapshot.power;
  }
  function inner(hc: number) {
    const hp = partialOrder.getGreatestPred(C, hc);
    assert(hp !== undefined, 'this should never happen.');
    function getHC_() {
      const tsHC = blocks[C].get(hc).t;
      // Get earliest height on consumer
      // that a VSC received at hc could mature
      const heights = Array.from(blocks[C].keys()).sort((a, b) => a - b);
      for (let i = 0; i < heights.length; i++) {
        const hc_ = heights[i];
        if (tsHC + UNBONDING_SECONDS_C <= blocks[C].get(hc_).t) {
          return hc_;
        }
      }
      return undefined;
    }
    const hc_ = getHC_();
    let hp_ = undefined;
    if (hc_ !== undefined) {
      hp_ = partialOrder.getLeastSucc(C, hc_);
    }
    let limit = Math.max(...Array.from(blocks[P].keys())) + 1;
    if (hp_ !== undefined) {
      // If provider receives maturation
      // only check property up to and not including
      // the block at which received.
      limit = hp_;
    }
    for (let h = hp; h < limit; h++) {
      for (let i = 0; i < NUM_VALIDATORS; i++) {
        const powerP = powerProvider(blocks[P].get(h));
        const powerC = powerConsumer(blocks[C].get(hc));
        if (powerC[i] !== undefined) {
          if (powerP[i] < powerC[i]) {
            return false;
          }
        }
      }
    }
    return true;
  }
  return _.reduce(
    Array.from(blocks[C].keys()),
    (good, hc) => good && inner(hc),
    true,
  );
}

export {
  PartialOrder,
  Block,
  BlockHistory,
  stakingWithoutSlashing,
  bondBasedConsumerVotingPower,
};
