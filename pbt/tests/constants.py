from enum import Enum


P = "provider"
C = "consumer"

UNBONDING_TIME = 5
NUM_VALIDATORS = 4
MAX_VALIDATORS = 2  # allows jailing 2 validators

ZERO_TIMEOUT_HEIGHT = 10000
CCV_TIMEOUT_TIMESTAMP = 10000

SLASH_FACTOR_DOWNTIME = 1 / 4
JAIL_TIME = 10000


class Status(Enum):
    BONDED = "bonded"
    UNBONDING = "unbonding"
    UNBONDED = "unbonded"
