from enum import Enum


class Events:
    class Event(str, Enum):
        REBOND_UNVAL = "rebond_unval"
        COMPLETE_UNVAL_IN_ENDBLOCK = "complete_unval_in_endblock"
        COMPLETE_UNVAL_NOW = "complete_unval_now"
        SET_UNVAL_HOLD_FALSE = "set_unval_hold_false"
        COMPLETE_UNDEL_IN_ENDBLOCK = "complete_undel_in_endblock"
        COMPLETE_UNDEL_NOW = "complete_undel_now"
        SET_UNDEL_HOLD_FALSE = "set_undel_hold_false"
        INVALID_EX_RATE = "invalid_ex_rate"
        INSUFFICIENT_TOKENS = "insufficient_tokens"
        INSUFFICIENT_SHARES = "insufficient_shares"
        SLASH_UNDEL = "slash_undel"
        SLASH_VAL = "slash_val"
        JAIL = "jail"
        SEND_DOWNTIME_SLASH_REQUEST = "send_downtime_slash_request"
        RECEIVE_DOWNTIME_SLASH_REQUEST = "receive_downtime_slash_request"
        RECEIVE_DOWNTIME_SLASH_ACK = "receive_downtime_slash_ack"
        SEND_DOUBLE_SIGN_SLASH_REQUEST = "send_double_sign_slash_request"
        RECEIVE_DOUBLE_SIGN_SLASH_REQUEST = "receive_double_sign_slash_request"
        DOWNTIME_SLASH_REQUEST_OUTSTANDING = "downtime_slash_request_outstanding"
        CONSUMER_UPDATE_POWER_POSITIVE = "consumer_update_power_positive"
        CONSUMER_UPDATE_POWER_ZERO = "consumer_update_power_zero"
        CONSUMER_NO_PENDING_CHANGES = "consumer_no_pending_changes"
        CONSUMER_SEND_MATURATION = "consumer_send_maturation"
        CONSUMER_NOT_ALL_MATURED = "consumer_not_all_matured"
        SEND_VSC_NOT_BECAUSE_CHANGE = "send_vsc_not_because_change"
        SEND_VSC_WITH_DOWNTIME_ACK = "send_vsc_with_downtime_ack"
        SEND_VSC_WITHOUT_DOWNTIME_ACK = "send_vsc_without_downtime_ack"
        SOME_UNDELS_EXPIRED_BUT_NOT_COMPLETED = "some_undels_expired_but_not_completed"
        SOME_UNVALS_EXPIRED_BUT_NOT_COMPLETED = "some_unvals_expired_but_not_completed"

    def __init__(self):
        self.events = []

    def add(self, e):
        assert isinstance(e, Events.Event)
        self.events.append(e)
