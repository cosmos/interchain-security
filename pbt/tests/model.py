from recordclass import recordclass
from copy import deepcopy
from collections import defaultdict
from .constants import *

Undelegation = recordclass(
    "Undelegation",
    [
        "val",
        "creation_height",
        "completion_time",
        "balance",
        "initial_balance",
        "on_hold",
        "op_id",
        "expired",
    ],
)

Unval = recordclass(
    "Unval",
    ["val", "unbonding_height", "unbonding_time", "on_hold", "op_id", "expired"],
)

Vsc = recordclass("Vsc", ["vsc_id", "changes", "slash_acks"])

VscMatured = recordclass("VscMatured", ["vsc_id"])

Slash = recordclass("Slash", ["val", "power", "vsc_id", "is_downtime"])


class Outbox:
    Packet = recordclass(
        "Packet", ["timeout_height", "timeout_timestamp", "data", "send_height"]
    )

    def create_packet(data, send_height):
        zero_timeout_height = ZERO_TIMEOUT_HEIGHT
        ccv_timeout_timestamp = CCV_TIMEOUT_TIMESTAMP
        return Outbox.Packet(
            zero_timeout_height, ccv_timeout_timestamp, data, send_height
        )

    def __init__(self, model, chain):
        self.m = model
        self.chain = chain
        self.fifo = []
        self.fifo_committed = []

    def add(self, data):
        # send height is used to establish ordering
        # between blocks on different chains
        self.fifo.append(Outbox.create_packet(data, self.m.h[self.chain]))

    def is_empty(self):
        return 0 == len(self.fifo_committed)

    def consume(self):
        ret = self.fifo_committed
        self.fifo_committed = []
        return ret

    def commit(self):
        self.fifo_committed.extend(self.fifo)
        self.fifo = []


class Staking:
    """Provider staking"""

    def __init__(self, model):
        self.m = model
        # the number of shares the delegator has in the validator
        # simply hardcoded to match what driver starts with
        # denominated in shares
        self.delegation = [4, 3, 2, 1]
        # tokens = shares before any slashing or rewards happen
        # 1 token is self delegated by validators
        # denominated in tokens, but use 1-1 exchange rate
        self.tokens = [x + 1 for x in self.delegation]
        # validator status
        self.status = [Status.BONDED, Status.BONDED, Status.UNBONDED, Status.UNBONDED]
        # unbonding delegations (undels)
        self.undelegationQ = []
        # unbonding validators (unvals)
        self.validatorQ = []
        # jailed? If yes, timestamp of unjailing
        self.jailed = [None] * NUM_VALIDATORS
        # delegator balance, hardcoded
        self.delegator_tokens = 10000000000000000000
        # used to track unbonding and redelegation entries, as well as
        # map to unbonding validators, in order to track on_hold
        self.unbonding_op_id = 0
        # used to compute val set changes
        # maps validators to power
        self.changes = {}
        # validators of last block (lastValidators)
        self.last_vals = self.new_vals()
        # required for computation of self.changes
        self.last_tokens = list(self.tokens)

    def begin_block(self):
        pass

    def end_block(self):

        """
        Process undelegations
        """

        expired_undels = [
            e
            for e in self.undelegationQ
            if e.completion_time <= self.m.t[P] and not e.expired
        ]

        for e in expired_undels:
            e.expired = True

        completed_undels = [e for e in expired_undels if not e.on_hold]

        self.undelegationQ = [
            e for e in self.undelegationQ if e not in completed_undels
        ]

        self.delegator_tokens += sum(e.balance for e in completed_undels)

        """
        Process validators
        """

        old_vals = self.last_vals
        new_vals = self.new_vals()

        for i in new_vals:
            self.status[i] = Status.BONDED
            self.validatorQ = [e for e in self.validatorQ if e.val != i]

        expired_unvals = [
            e
            for e in self.validatorQ
            if e.unbonding_time <= self.m.t[P]
            and e.unbonding_height <= self.m.h[P]
            and not e.expired
        ]

        for e in expired_unvals:
            e.expired = True

        completed_unvals = [e for e in expired_unvals if not e.on_hold]

        for e in completed_unvals:
            self.status[e.val] = Status.UNBONDED

        new_unvals = []
        for i in set(old_vals) - set(new_vals):
            new_unvals.append(
                Unval(
                    i,
                    self.m.h[P],
                    self.m.t[P] + UNBONDING_TIME,
                    True,
                    self.unbonding_op_id,
                    False,
                )
            )
            self.after_unbonding_initiated(self.unbonding_op_id)
            self.unbonding_op_id += 1
            self.status[i] = Status.UNBONDING

        self.validatorQ = [
            e for e in self.validatorQ if e not in completed_unvals
        ].extend(new_vals)

        self.changes = {}
        for i in new_vals:
            if self.tokens[i] != self.last_tokens[i]:
                # if validator power changed
                self.changes[i] = self.tokens[i]
        for i in set(new_vals) - set(old_vals):
            self.changes[i] = self.tokens[i]
        for i in set(old_vals) - set(new_vals):
            # if validator no longer bonded, set '0' power
            self.changes[i] = 0

        self.last_vals = new_vals
        self.last_tokens = list(self.tokens)

    def delegate(self, val, amt):
        # TODO: check division rounding in sdk
        if self.invalid_ex_rate(val):
            return  # invalid ex rate
        issued_shares = (self.shares(val) * amt) // self.tokens[val]
        self.delegator_tokens -= amt
        self.tokens[val] += amt
        self.delegation[val] += issued_shares

    def undelegate(self, val, amt):
        # TODO: check division rounding in sdk
        if self.tokens[val] < 1:

            return  # insufficient tokens
        shares = (self.shares(val) * amt) // self.tokens[val]
        if self.delegation[val] < shares:
            return  # insufficient shares
        # TODO: check order of arithmetic
        issued_tokens = (shares * self.tokens[val]) // self.shares(val)
        self.tokens[val] -= issued_tokens
        self.delegation[val] -= shares

        op_id = self.unbonding_op_id
        self.unbonding_op_id += 1
        und = Undelegation(
            val,
            self.m.h[P],
            self.m.t[P] + UNBONDING_TIME,
            issued_tokens,
            issued_tokens,
            True,
            op_id,
            False,
        )
        self.undelegationQ.append(und)
        self.m.ccv_p.after_unbonding_initiated(op_id)

    def slash(self, val, infraction_height, power, factor):
        # This assumes 1:1 tokens:power

        def valid(e):
            return (infraction_height <= e.creation_height) and (
                self.m.t[P] < e.completion_time or e.on_hold
            )

        ubds = [e for e in self.undelegationQ if e.val == val and valid(e)]

        amt = int(power * factor)
        remaining = amt
        if infraction_height < self.m.h[P]:
            for e in ubds:
                slashed = int(factor * e.initial_balance)
                remaining -= slashed
                e.balance = max(0, e.balance - slashed)

        to_burn = min(max(remaining, 0), self.tokens[val])
        self.tokens[val] -= to_burn

    def jail_until(self, val, timestamp):
        self.jailed[val] = timestamp

    def new_vals(self):
        def valid(i):
            """
            We model a chain where a validator
            has a minSelfDelegation of 1.
            """
            return 1 <= self.tokens[i] and self.jailed[i] is None

        # sort first by power descending and then lexico
        vals = list(range(NUM_VALIDATORS))

        assert all(0 <= t for t in self.tokens)
        # stable
        vals.sort(key=lambda i: -self.tokens[i])
        vals = [i for i in vals if valid(i)]

        return vals[:MAX_VALIDATORS]

    def shares(self, val):
        # Add 1 for minSelfDelegation = 1
        return self.delegation[val] + 1

    def invalid_ex_rate(self, val):
        return self.tokens[val] == 0 and 0 < self.shares(val)

    def unbonding_can_complete(self, op_id):
        if op_id in self.unbonding_op_id_to_val:
            val = self.unbonding_op_id_to_val[op_id]
            del self.unbonding_op_id_to_val[op_id]
            assert val not in self.unbonding_op_id_to_val.values()
            # TODO: This is a bit strange but copying cosmos-sdk code verbatim for now
            # I should check if that's the right approach
            assert isinstance(self.unbonding_height[val], int), (
                val,
                self.unbonding_height,
                self.validatorQ,
                self.unbonding_op_id_to_val,
            )
            assert isinstance(self.unbonding_time[val], int)
            if (
                self.unbonding_height[val] < self.m.h[P]
                and self.unbonding_time[val] < self.m.t[P]
            ):
                self.status[val] = Status.UNBONDED
                self.unbonding_height[val] = None
                self.unbonding_time[val] = None
                self.validatorQ = [v for v in self.validatorQ if v != val]
            self.on_hold[val] = False
        for e in self.undelegationQ:
            # In contrast to the code, I store op_id with the entry
            # allowing me to do this loop
            if e.op_id == op_id:
                if self.m.t[P] < e.completion_time:
                    e.on_hold = False
                else:
                    self.delegator_tokens += e.balance
                    self.undelegationQ = [x for x in self.undelegationQ if x != e]

    def validator_changes(self):
        # Called by CCV, return changed validator powers
        return self.changes


class CCVProvider:
    def __init__(self, model):
        self.m = model

        # TODO: I should check this
        self.initial_height = 0
        self.vsc_id = 0
        self.vsc_id_to_h = {}
        self.vsc_id_to_unbonding_op_ids = defaultdict(set)
        self.slash_requests = []

    def begin_block(self):
        pass

    def end_block(self):

        changes = self.m.staking.validator_changes()

        if 0 < len(changes) or 0 < len(self.vsc_id_to_unbonding_op_ids[self.vsc_id]):
            data = Vsc(self.vsc_id, changes, self.slash_requests)
            self.slash_requests = []
            self.m.outbox_p.add(data)

        self.vsc_id_to_h[self.vsc_id] = self.m.h[P] + 1
        self.vsc_id += 1

    def on_receive(self, data):
        if isinstance(data, VscMatured):
            self.on_receive_vsc_matured(data)
        if isinstance(data, Slash):
            self.on_receive_slash(data)

    def on_receive_vsc_matured(self, data):
        for op_id in self.vsc_id_to_unbonding_op_ids[data.vsc_id]:
            self.m.staking.unbonding_can_complete(op_id)
        del self.vsc_id_to_unbonding_op_ids[data.vsc_id]

    def on_receive_slash(self, data):
        infraction_height = None
        if data.vsc_id == 0:
            infraction_height = self.initial_height
        else:
            infraction_height = self.vsc_id_to_h[data.vsc_id]

        # in the spec, these are slashing module calls but they
        # pass straight through to the staking module
        self.m.staking.slash(
            data.val, infraction_height, data.power, SLASH_FACTOR_DOWNTIME
        )
        self.m.staking.jail_until(data.val, self.m.t[P] + JAIL_TIME)

        self.slash_requests.append(data.val)

    def after_unbonding_initiated(self, op_id):
        self.vsc_id_to_unbonding_op_ids[self.vsc_id].add(op_id)


class CCVConsumer:
    def __init__(self, model):
        self.m = model
        # Maps height to vsc_id, TODO: check
        self.h_to_vsc_id = {0: 0, 1: 0}
        # List of dictionaries
        self.pending_changes = []
        # Maps vsc_id to unbonding time (timestamp)
        self.maturing_vscs = {}
        # Maps val to bool
        self.outstanding_downtime = {i: False for i in range(NUM_VALIDATORS)}
        # Maps val to power
        self.power = {i: self.m.staking.tokens[i] for i in self.m.staking.last_vals}

    def begin_block(self):
        self.h_to_vsc_id[self.m.h[C] + 1] = self.h_to_vsc_id[self.m.h[C]]

    def end_block(self):
        if len(self.pending_changes) < 1:
            return

        matured = [
            vsc_id for vsc_id, time in self.maturing_vscs.items() if time <= self.m.t[C]
        ]

        for vsc_id in matured:
            data = VscMatured(vsc_id)
            self.m.outbox_c.add(data)
            del self.maturing_vscs[vsc_id]

        def aggregate_changes():
            # Flatten the changes
            latest = {}
            for u in self.pending_changes:
                latest = latest | u
            return latest

        changes = aggregate_changes()

        for val, power in changes.items():
            self.power.pop(val, None)
            if 0 < power:
                self.power[val] = power

        self.pending_changes = []

    def on_receive(self, data):
        if isinstance(data, Vsc):
            self.on_receive_vsc(data)

    def on_receive_vsc(self, data):
        self.h_to_vsc_id[self.m.h[C] + 1] = data.vsc_id

        # pending slash requests would be sent here, but
        # we model an established system, assuming a
        # successfull handshake.

        self.pending_changes.append(data.changes)

        self.maturing_vscs[data.vsc_id] = self.m.t[C] + UNBONDING_TIME

        for val in data.slash_acks:
            self.outstanding_downtime[val] = False

    def send_slash_request(self, val, power, infraction_height, is_downtime):

        if is_downtime and self.outstanding_downtime[val]:
            return

        data = Slash(val, power, self.h_to_vsc_id[infraction_height], is_downtime)
        self.m.outbox_c.add(data)
        if is_downtime:
            self.outstanding_downtime[val] = True


class Model:
    def __init__(self, blocks):

        # global time
        self.T = 0
        # height on each chain
        self.h = {P: 0, C: 0}
        # time for block self.h[x], none if must BeginBlock
        self.t = {P: 0, C: 0}

        # FIFO - front of queue is ix 0
        self.outbox_p = Outbox(self, P)
        self.outbox_c = Outbox(self, C)

        self.staking = Staking(self)
        self.ccv_p = CCVProvider(self)
        self.ccv_c = CCVConsumer(self)

        # Used to record committed blocks
        self.blocks = blocks

        # Record a happens-before relationship between genesis blocks
        # provider h0 happens before consumer h0
        self.blocks.partial_order.deliver(C, 0, 0)

        # simulate the committing of the genesis block and beginning of
        # a new block
        self.blocks.commit_block(P, self.snapshot())
        self.blocks.commit_block(C, self.snapshot())
        self.increase_seconds(1)
        self.must_begin_block = {P: True, C: True}

    class Snapshot:
        def __init__(self, init):
            for k, v in init.items():
                setattr(self, k, v)

    def snapshot(self):
        d = vars(deepcopy(self))
        del d["blocks"]
        return Model.Snapshot(deepcopy(d))

    def has_undelivered(self, chain):
        if chain == P:
            return not self.outbox_c.is_empty()
        if chain == C:
            return not self.outbox_p.is_empty()

    def idempotent_begin_block(self, chain):
        if self.must_begin_block[chain]:
            self.must_begin_block[chain] = False
            self.h[chain] += 1
            self.t[chain] = self.T
            if chain == P:
                pass
            if chain == C:
                self.ccv_c.begin_block()

    def delegate(self, val, amt):
        self.idempotent_begin_block(P)
        return self.staking.delegate(val, amt)

    def undelegate(self, val, amt):
        self.idempotent_begin_block(P)
        return self.staking.undelegate(val, amt)

    def end_block(self, chain):
        self.idempotent_begin_block(chain)
        if chain == P:
            self.staking.end_block()
            self.ccv_p.end_block()
            self.outbox_p.commit()
        if chain == C:
            self.ccv_c.end_block()
            self.outbox_c.commit()
        # Forces a begin_block as next action
        self.must_begin_block[chain] = True
        self.blocks.commit_block(chain, self.snapshot())

    def increase_seconds(self, seconds):
        self.T += seconds

    def deliver(self, chain):
        self.idempotent_begin_block(chain)
        if chain == P:
            for p in self.outbox_c.consume():
                self.blocks.partial_order.deliver(P, p.send_height, self.h[P])
                self.ccv_p.on_receive(p.data)
        if chain == C:
            for p in self.outbox_p.consume():
                self.blocks.partial_order.deliver(C, p.send_height, self.h[C])
                self.ccv_c.on_receive(p.data)

    def provider_slash(self, val, infraction_height, power, factor):
        self.idempotent_begin_block(P)
        self.staking.slash(val, infraction_height, power, factor)

    def consumer_slash(self, val, power, infraction_height, is_downtime):
        self.idempotent_begin_block(C)
        self.ccv_c.send_slash_request(val, power, infraction_height, is_downtime)
