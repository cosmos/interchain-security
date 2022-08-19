const P = 'provider';
const C = 'consumer';
// The maximum number of blocks that a chain can advance
// This number cannot be too high because it is not allowed
// for the IBC client to expire.
const MAX_BLOCK_ADVANCES = 9;
// Block interval, set to mimic real life.
const BLOCK_INTERVAL_SECONDS = 5;
// Trusting period
const TRUSTING_SECONDS = MAX_BLOCK_ADVANCES * BLOCK_INTERVAL_SECONDS - 1;
// Unbonding period for consumer. Must be greater than TRUSTING_SECONDS
const UNBONDING_SECONDS_C = TRUSTING_SECONDS + 1;
// Unbonding period for provider. Must be greater than TRUSTING_SECONDS.
// Should be greater than UNBONDING_SECONDS_C
const UNBONDING_SECONDS_P =
  UNBONDING_SECONDS_C + 5 * BLOCK_INTERVAL_SECONDS;
// Total number of validators to model.
const NUM_VALIDATORS = 4;
// Maximum number of active validator at a given time. This should be less
// than NUM_VALIDATORS in order to test scenarios where validators
// join and leave the active set, or are jailed.
const MAX_VALIDATORS = 2; // allows jailing 2 validators
const ZERO_TIMEOUT_HEIGHT = 100000; // TODO: think I can delete it?
const CCV_TIMEOUT_TIMESTAMP = 100000; // TODO: think I can delete it?
// Slash factor for double signing. This is set to 0 in order to test slashing
// logic while avoiding divergence between model and SUT due to differences
// in numerical implementations.
const SLASH_DOUBLESIGN = 0;
// ^^
const SLASH_DOWNTIME = 0;
// Jail time. Unjailing is not modelled.
const JAIL_SECONDS = 999999999999999;
// Multiply all hardcoded units of currency by a fixed scalar.
const TOKEN_SCALAR = 10000;
// Initial token balance for the (sole) delegator account. Should
// be large enough to allow unlimited delegate actions.
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
  BLOCK_INTERVAL_SECONDS as BLOCK_SECONDS,
  TOKEN_SCALAR,
  INITIAL_DELEGATOR_TOKENS,
  MAX_BLOCK_ADVANCES,
};
