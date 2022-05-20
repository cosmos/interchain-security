import os
import shutil
import time
import copy
import json
from .model import Model
from .constants import *
from .actions import *
from .properties import *
from recordclass import asdict


class Trace:
    def __init__(self):
        self.actions = []
        self.states = []

    def add_action(self, action):
        self.actions.append(action)

    def add_consequence(self, model_after_action):
        self.states.append(copy.deepcopy(model_after_action))

    def json(self):
        return {
            "actions": [
                {"kind": e.__class__.__name__} | asdict(e) for e in self.actions
            ],
            "states": [e.json() for e in self.states],
        }

    def write(self, fn):
        with open(fn, "w") as fd:
            obj = self.json()
            fd.write(json.dumps(obj, indent=2))


class Driver:
    def __init__(self, model, trace):
        self.m = model
        self.trace = trace
        self.shaper = Shaper(self.m)

    def action(self):
        return self.shaper.action()

    def do_action(self, a):
        self.trace.add_action(a)
        if isinstance(a, Delegate):
            self.m.delegate(a.val, a.amt)
        if isinstance(a, Undelegate):
            self.m.undelegate(a.val, a.amt)
        if isinstance(a, JumpNBlocks):
            for _ in range(a.n):
                for c in a.chains:
                    assert c in {P, C}
                    """
                    BeginBlock is forced before each action, if
                    necessary, and is not explicitly called.
                    """
                    self.m.end_block(c)
                self.m.increase_seconds(a.seconds_per_block)
        if isinstance(a, Deliver):
            self.m.deliver(a.chain)
        if isinstance(a, ProviderSlash):
            self.m.provider_slash(a.val, a.height, a.power, a.factor)
        if isinstance(a, ConsumerSlash):
            self.m.consumer_slash(a.val, a.power, a.height, a.is_downtime)
        self.trace.add_consequence(self.m)


def load_actions_for_debugging():
    obj = None
    with open("debug.json", "r") as fd:
        obj = json.loads(fd.read())
    return [action_from_json(a) for a in obj["actions"]]


def test_dummy():
    debug = False
    GOAL_TIME_MINS = 20
    NUM_ACTIONS = 20

    shutil.rmtree("traces/")
    os.makedirs("traces/")

    num_runs = 100000
    elapsed = 0
    i = 0
    while i < num_runs:
        i += 1
        if not debug and 10 < elapsed:
            avg = elapsed / i
            num_runs = GOAL_TIME_MINS * 60 / avg
        t_start = time.time()

        trace = Trace()
        model = Model()
        d = Driver(model, trace)
        actions = None
        if debug:
            actions = load_actions_for_debugging()
        for i in range(len(actions) if debug else NUM_ACTIONS):
            a = actions[i] if debug else d.action()
            try:
                d.do_action(a)
            except Exception as e:
                trace.write("debug.json")
                assert False
        try:
            assert staking_without_slashing(trace)
            assert bond_based_consumer_voting_power(trace)
        except Exception as e:
            trace.write("debug.json")
            assert False

        t_end = time.time()
        elapsed += t_end - t_start

        # trace.write(f"traces/trace_{i}.json")
    print("Ran {i} runs")
