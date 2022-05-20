from .actions import *
from .constants import *


def staking_without_slashing(trace):
    """
    The total number of tokens in the system is constant
    if there is no slashing.
    """
    for a in trace.actions:
        if isinstance(a, ProviderSlash):
            return True
        if isinstance(a, ConsumerSlash):
            return True
    if len(trace.states) < 2:
        return True
    initial = trace.states[0]
    states = trace.states[1:]

    def value(s):
        s = s.staking
        x = s.delegator_tokens
        x += sum(s.tokens)
        x += sum(u.balance for u in s.undelegationQ)
        return x

    v = value(initial)
    for s in states:
        if value(s) != v:
            return False

    return True


def bond_based_consumer_voting_power(trace):
    partial_order = trace.states[-1].verify.partial_order
    blocks = trace.states[-1].verify.blocks

    def inner(hc):

        hp = partial_order.get_greatest_predecessor(C, hc)
        if hp is None:
            assert False, "No greatest predecessor for consumer block found!"

        def get_hc_(ts_hc):
            heights = sorted(blocks[C].keys())
            for hc_ in heights:
                if ts_hc + UNBONDING_TIME <= blocks[C][hc_].t:
                    return hc_
            return None

        hc_ = get_hc_(blocks[C][hc].t)

        hp_ = None
        if hc_ is not None:
            # Matured on C
            hp_ = partial_order.get_least_successor(C, hc_)
        # default: P never received maturation, check all remaining blocks
        limit = max(blocks[P].keys())
        if hp_ is not None:
            # P received maturation
            limit = hp_ = 1
        for h in range(hp, limit + 1):
            for i in range(NUM_VALIDATORS):
                if i in blocks[C][hc].power:
                    if blocks[P][h].compare[i] < blocks[C][hc].power[i]:
                        # property violation!
                        return False
        return True

    for hc in blocks[C].keys():
        if not inner(hc):
            return False
    return True
