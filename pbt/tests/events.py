from enum import StrEnum


class Events:
    class Event(StrEnum):
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
        SLASH = "slash"
        JAIL = "jail"
        SEND_DOWNTIME_SLASH_REQUEST = "send_downtime_slash_request"
        RECEIVE_DOWNTIME_SLASH_REQUEST = "receive_downtime_slash_request"
        RECEIVE_DOWNTIME_SLASH_ACK = "receive_downtime_slash_ack"
        SEND_DOUBLE_SIGN_SLASH_REQUEST = "send_double_sign_slash_request"
        RECEIVE_DOUBLE_SIGN_SLASH_REQUEST = "receive_double_sign_slash_request"
        DOWNTIME_SLASH_REQUEST_OUTSTANDING = "downtime_slash_request_outstanding"
        CONSUMER_UPDATE_POWER = "consumer_update_power"

    def __init__(self):
        self.events = []

    def add(self, e):
        assert isinstance(e, Events.Event)
        self.events.add(e)
