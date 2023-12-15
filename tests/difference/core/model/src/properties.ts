import { strict as assert } from 'node:assert';
import _ from 'underscore';
import {
  P,
  C,
  UNBONDING_SECONDS_C,
  NUM_VALIDATORS,
} from './constants.js';
import {
  PropertiesSystemState,
  Chain,
  CommittedBlock,
  Status,
} from './common.js';

/**
 * Queries and data structures in this file are currently naive
 * and below optimal.
 * Partial order queries and other total order queries in
 * bond-based-consumer-voting-power can be done with binary searches.
 */

/**
 * Data structure used to store a partial order of blocks. The partial order
 * is induced by packet delivery for blocks on different chains, and by height
 * for blocks on the same chain.
 * See https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/system_model_and_properties.md#system-properties
 */
class PartialOrder {
  // map chain -> block height in chain -> block height in counterparty chain
  greatestPred: Record<Chain, Map<number, number>> = {
    provider: new Map(),
    consumer: new Map(),
  };
  // map chain -> block height in chain -> block height in counterparty chain
  leastSucc: Record<Chain, Map<number, number>> = {
    provider: new Map(),
    consumer: new Map(),
  };

  /**
   * Mark the delivery of a packet. Induces a partial order between blocks
   * on different chains.
   * @param receiverChain chain receiving packet
   * @param sendHeight send height on sending chain
   * @param receiveHeight receive height on receiving chain
   */
  deliver = (
    receiverChain: Chain,
    sendHeight: number,
    receiveHeight: number,
  ) => {
    let h = sendHeight;
    if (this.greatestPred[receiverChain].has(receiveHeight)) {
      h = Math.max(
        this.greatestPred[receiverChain].get(receiveHeight) as number,
        h,
      );
    }
    this.greatestPred[receiverChain].set(receiveHeight, h);
    const senderChain = receiverChain === P ? C : P;
    h = receiveHeight;
    if (this.leastSucc[senderChain].has(sendHeight)) {
      h = Math.min(
        this.leastSucc[senderChain].get(sendHeight) as number,
        h,
      );
    }
    this.leastSucc[senderChain].set(sendHeight, h);
  };

  /**
   * @param chain chain of block
   * @param height height of block
   * @returns Returns the height greatest predecessor block on the counterparty
   * chain if it exists, else undefined.
   */
  getGreatestPred = (
    chain: Chain,
    height: number,
  ): number | undefined => {
    const it = this.greatestPred[chain].keys();
    let bestH = -1;
    let bestV = -1;
    let result = it.next();
    while (!result.done) {
      const h = result.value;
      if (bestH < h && h <= height) {
        bestH = h;
        bestV = this.greatestPred[chain].get(h) as number;
      }
      result = it.next();
    }
    if (bestV === -1) {
      // No greatest predecessor exists.
      return;
    }
    return bestV;
  };

  /**
   *
   * @param chain chain of block
   * @param height height of block
   * @returns Returns the height of the least successor block on the counterparty
   * chain if it exists, else undefined.
   */
  getLeastSucc = (chain: Chain, height: number): number | undefined => {
    const it = this.leastSucc[chain].keys();
    let bestH = 100000000000000; // Infinity
    let bestAnswer = -1;
    let result = it.next();
    while (!result.done) {
      const h = result.value;
      if (h < bestH && height <= h) {
        bestH = h;
        bestAnswer = this.leastSucc[chain].get(h) as number;
      }
      result = it.next();
    }
    if (bestAnswer === -1) {
      // No least successor exists.
      return;
    }
    return bestAnswer;
  };
}

class BlockHistory {
  partialOrder = new PartialOrder();
  blocks: Record<Chain, Map<number, CommittedBlock>> = {
    provider: new Map(),
    consumer: new Map(),
  };
  /**
   * Mark state as permanently committed to the blockchain.
   * @param chain
   * @param propertiesSystemState
   */
  commitBlock = (chain: Chain, propertiesSystemState: PropertiesSystemState) => {
    const h = propertiesSystemState.h[chain];
    const b: CommittedBlock = {
      chain,
      propertiesSystemState: propertiesSystemState,
    };
    this.blocks[chain].set(h, b);
  };
}

function sum(arr: number[]): number {
  return arr.reduce((sum: number, x: number) => sum + x, 0);
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
  const blocks = Array.from(hist.blocks[P].entries())
    .sort((a, b) => a[0] - b[0])
    .map((e) => e[1])
    .map((b) => b.propertiesSystemState);

  function value(e: PropertiesSystemState) {
    let x = e.delegatorTokens;
    x += sum(e.tokens);
    x += sum(e.undelegationQ.map((e) => e.balance));
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
 * Checks the validator set replication property as defined
 * https://github.com/cosmos/ibc/blob/main/spec/app/ics-028-cross-chain-validation/system_model_and_properties.md#system-properties
 *
 * @param hist A history of blocks.
 * @returns Is the property satisfied?
 */
function validatorSetReplication(hist: BlockHistory): boolean {
  const blocks = hist.blocks;
  let good = true;

  // Each committed block on the consumer chain has a last vscID
  // received that informs the validator set at the NEXT height.
  // Thus, on every received VSCPacket with vscID at height H, 
  // the consumer sets hToVscID[H+1] to vscID. 
  //
  // The consumer valset is exactly the valset on the provider
  // at the NEXT height after the vscID was sent.
  // Thus, on every sent VSCPacket with vscID at height H,
  // the provider sets vscIDtoH[vscID] to H+1 
  //
  // As a result, for every height hC on the consumer, the active 
  // valset was last updated by the VSCPacket with ID vscID = hToVscID[hc]. 
  // This packet was sent by the provider at height hP-1, with hP = vscIDtoH[vscID]. 
  // This means that the consumer valset at height hC MUST match
  // the provider valset at height hP.
  // 
  // We compare these valsets, which are committed in blocks 
  // hC-1 and hP-1, respectively (the valset is always used at the NEXT height).
  for (const [hC, b] of blocks[C]) {
    if (hC < 1) {
      // The model starts at consumer height 0, so there is
      // no committed block at height - 1. This means it does
      // not make sense to try to check the property for height 0.
      continue
    }
    const snapshotC = b.propertiesSystemState;
    // Get the vscid of the last update which dictated
    // the consumer valset valsetC committed at hC-1
    const vscid = snapshotC.hToVscID[hC];
    // The VSU packet was sent at height hP-1
    const hP = snapshotC.vscIDtoH[vscid];
    // Compare the validator sets at hC-1 and hP-1
    const valsetC = blocks[C].get(hC - 1)!.propertiesSystemState.consumerPower;
    // The provider set is implicitly defined by the status and tokens (power)
    if (hP < 1) {
      // The model starts at provider height 0, so there is
      // no committed block at height - 1. This means it does not
      // make sense to try to check the property for height 0.
      continue
    }
    const snapshotP = blocks[P].get(hP - 1)!.propertiesSystemState;
    const statusP = snapshotP.status;
    const tokensP = snapshotP.tokens;
    assert(valsetC.length === statusP.length, 'this should never happen.');
    assert(valsetC.length === tokensP.length, 'this should never happen.');
    valsetC.forEach((power, i) => {
      if (power !== null) { // null means the validator is not in the set
        // Check that the consumer power is strictly equal to the provider power
        good = good && (tokensP[i] === power);
      }
    })
    statusP.forEach((status, i) => {
      if (status === Status.BONDED) {
        const power = tokensP[i];
        // Check that the consumer power is strictly equal to the provider power
        good = good && (valsetC[i] === power);
      }
      else {
        // Ensure that the consumer validator set does not contain a non-bonded validator
        good = good && (valsetC[i] === null);
      }
    })

  }
  return good;
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
  /**
   * @param block to compute validator voting powers for
   * @param hp is the earliest height for unbondings to account for
   * @returns burnable voting power for each validator on the Provider chain
   */
  function powerProvider(block: CommittedBlock, hp: number): number[] {
    return _.range(NUM_VALIDATORS).map((i) => {
      let x = 0;
      if (block.propertiesSystemState.status[i] !== Status.UNBONDED) {
        x += block.propertiesSystemState.tokens[i];
      }
      x += sum(
        block.propertiesSystemState.undelegationQ
          .filter((e) => e.val === i)
          .filter((e) => hp <= e.creationHeight)
          .map((e) => e.initialBalance),
      );
      return x;
    });
  }
  function powerConsumer(block: CommittedBlock) {
    return block.propertiesSystemState.consumerPower;
  }
  function inner(hc: number): boolean {
    const hp = partialOrder.getGreatestPred(C, hc);
    assert(hp !== undefined, 'this should never happen.');
    function getHC_() {
      const tsHC = (blocks[C].get(hc) as CommittedBlock).propertiesSystemState
        .t[C];
      // Get earliest height on consumer
      // that a VSC received at hc could mature
      const heights = Array.from(blocks[C].keys()).sort((a, b) => a - b);
      for (let i = 0; i < heights.length; i++) {
        const hc_ = heights[i];
        if (
          tsHC + UNBONDING_SECONDS_C <=
          (blocks[C].get(hc_) as CommittedBlock).propertiesSystemState.t[C]
        ) {
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
        const powerP = powerProvider(
          blocks[P].get(h) as CommittedBlock,
          hp + 1,
        );
        const powerC = powerConsumer(blocks[C].get(hc) as CommittedBlock);
        if (powerC[i] !== null) {
          if (powerP[i] < (powerC[i] as number)) {
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
  CommittedBlock,
  BlockHistory,
  stakingWithoutSlashing,
  bondBasedConsumerVotingPower,
  validatorSetReplication,
};
