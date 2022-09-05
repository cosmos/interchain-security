import { ModelInitState, Status } from './common.js';

const P = 'provider';
const C = 'consumer';

// Block interval, set to mimic real life.
const BLOCK_SECONDS = 6;
// Trusting period
const TRUSTING_SECONDS = 49;
// Unbonding period for consumer. Must be greater than TRUSTING_SECONDS
const UNBONDING_SECONDS_C = 50;
// Unbonding period for provider. Must be greater than TRUSTING_SECONDS.
// Should be greater than UNBONDING_SECONDS_C
const UNBONDING_SECONDS_P = 70;

// Total number of validators to model.
const NUM_VALIDATORS = 4;
// Maximum number of active validator at a given time. This should be less
// than NUM_VALIDATORS in order to test scenarios where validators
// join and leave the active set, or are jailed.
const MAX_VALIDATORS = 2; // allows jailing 2 validators
// Slash factor for double signing. This is set to 0 in order to test slashing
// logic while avoiding divergence between model and SUT due to differences
// in numerical implementations.
const SLASH_DOUBLESIGN = 0;
// ^^
const SLASH_DOWNTIME = 0;
// Jail time. Unjailing is not modelled.
const JAIL_SECONDS = 999999999999999;
// Initial token balance for the (sole) delegator account. Should
// be large enough to allow unlimited delegate actions.
const INITIAL_DELEGATOR_TOKENS = 10000000000000;

const DELEGATE_AMT_MIN = 1000;
const DELEGATE_AMT_MAX = 5000;
const UNDELEGATE_AMT_MIN = 1000;
const UNDELEGATE_AMT_MAX = 5000;
const ISDOWNTIME_PROBABILITY = 0.5;
const MAX_NUM_PACKETS_FOR_DELIVER = 6;

const MODEL_INIT_STATE: ModelInitState = {
  h: { provider: 0, consumer: 0 },
  t: { provider: 0, consumer: 0 },
  ccvC: {
    hToVscID: { 0: 0, 1: 0 },
    pendingChanges: [],
    maturingVscs: new Map(),
    outstandingDowntime: [false, false, false, false],
    consumerPower: [5000, 4000, undefined, undefined],
  },
  ccvP: {
    initialHeight: 0,
    vscID: 0,
    vscIDtoH: {},
    vscIDtoOpIDs: new Map(),
    downtimeSlashAcks: [],
    tombstoned: [false, false, false, false],
    matureUnbondingOps: [],
  },
  staking: {
    delegation: [4000, 3000, 2000, 1000],
    tokens: [5000, 4000, 3000, 2000],
    status: [
      Status.BONDED, // Bonded as per the delegation above
      Status.BONDED, // ^^
      Status.UNBONDED, // Unbonded as per MAX_VALIDATORS
      Status.UNBONDED, // ^^
    ],
    undelegationQ: [],
    validatorQ: [],
    jailed: [undefined, undefined, undefined, undefined],
    delegatorTokens: INITIAL_DELEGATOR_TOKENS,
    opID: 0,
    changes: {},
    lastVals: [0, 1],
    lastTokens: [5000, 4000, 3000, 2000],
  },
};

/*
 * Used to track various semantic events that occur during model exploration.
 */
enum Event {
  REBOND_UNVAL = 'rebond_unval',
  COMPLETE_UNVAL_IN_ENDBLOCK = 'complete_unval_in_endblock',
  SET_UNVAL_HOLD_FALSE = 'set_unval_hold_false',
  COMPLETE_UNDEL_IN_ENDBLOCK = 'complete_undel_in_endblock',
  COMPLETE_UNDEL_IMMEDIATE = 'complete_undel_immediate',
  SET_UNDEL_HOLD_FALSE = 'set_undel_hold_false',
  INSUFFICIENT_SHARES = 'insufficient_shares',
  SLASH_UNDEL = 'slash_undel',
  JAIL = 'jail',
  SEND_DOWNTIME_SLASH_REQUEST = 'send_downtime_slash_request',
  RECEIVE_DOWNTIME_SLASH_REQUEST = 'receive_downtime_slash_request',
  RECEIVE_DOWNTIME_SLASH_ACK = 'receive_downtime_slash_ack',
  SEND_DOUBLE_SIGN_SLASH_REQUEST = 'send_double_sign_slash_request',
  CONSUMER_SEND_MATURATION = 'consumer_send_maturation',
  SEND_VSC_NOT_BECAUSE_CHANGE = 'send_vsc_not_because_change',
  SEND_VSC_WITH_DOWNTIME_ACK = 'send_vsc_with_downtime_ack',
  SEND_VSC_WITHOUT_DOWNTIME_ACK = 'send_vsc_without_downtime_ack',
  SOME_UNDELS_EXPIRED_BUT_NOT_COMPLETED = 'some_undels_expired_but_not_completed',
  RECEIVE_DOUBLE_SIGN_SLASH_REQUEST = 'receive_double_sign_slash_request',
  RECEIVE_SLASH_REQUEST_UNBONDED = 'receive_slash_request_unbonded',
  DOWNTIME_SLASH_REQUEST_OUTSTANDING = 'downtime_slash_request_outstanding',
  CONSUMER_UPDATE_VAL = 'consumer_update_val',
  CONSUMER_DEL_VAL = 'consumer_del_val',
  CONSUMER_ADD_VAL = 'consumer_add_val',
  MORE_THAN_ONE_THIRD_VAL_POWER_CHANGE = 'more_than_one_third_val_power_change',
}

export {
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
  Event,
  MODEL_INIT_STATE,
};
