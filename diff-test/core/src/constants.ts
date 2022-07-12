const P = 'provider';
const C = 'consumer';
const MAX_JUMPS = 3;
const BLOCK_SECONDS = 5;
const TRUSTING_SECONDS = MAX_JUMPS * BLOCK_SECONDS - 1;
const UNBONDING_SECONDS_C = TRUSTING_SECONDS + 1;
const UNBONDING_SECONDS_P = UNBONDING_SECONDS_C + 5 * BLOCK_SECONDS;
const NUM_VALIDATORS = 4;
const MAX_VALIDATORS = 2; // allows jailing 2 validators
const ZERO_TIMEOUT_HEIGHT = 100000;
const CCV_TIMEOUT_TIMESTAMP = 100000;
const SLASH_DOUBLESIGN = 1 / 2;
const SLASH_DOWNTIME = 1 / 4;
const JAIL_SECONDS = 999999999999999;
const TOKEN_SCALAR = 10000;
const INITIAL_DELEGATOR_TOKENS = 1000000000000000;

export {
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
};
