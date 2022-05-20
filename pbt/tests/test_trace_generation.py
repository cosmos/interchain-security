import pytest
import os
import shutil
import time
import copy
import json
from .model import Model
from .constants import *
from .properties import *
from recordclass import asdict

from .constants import *
from recordclass import recordclass
import random

Delegate = recordclass("Delegate", ["val", "amt"])
Undelegate = recordclass("Undelegate", ["val", "amt"])
JumpNBlocks = recordclass("JumpNBlocks", ["chains", "n", "seconds_per_block"])
Deliver = recordclass("Deliver", ["chain"])
ProviderSlash = recordclass("ProviderSlash", ["val", "power", "height", "factor"])
ConsumerSlash = recordclass("ConsumerSlash", ["val", "power", "height", "is_downtime"])


class Shaper:
    """
    Generates parameterized actions given implicit constraints derived
    from model state
    """

    def __init__(self, model):
        self.m = model
        self.delegated_since_block = {i: False for i in range(NUM_VALIDATORS)}
        self.undelegated_since_block = {i: False for i in range(NUM_VALIDATORS)}
        self.jailed = {i: False for i in range(NUM_VALIDATORS)}

    def action(self, json=None):

        if json:
            ctors = {
                c.__name__: c
                for c in [
                    Delegate,
                    Undelegate,
                    JumpNBlocks,
                    Deliver,
                    ProviderSlash,
                    ConsumerSlash,
                ]
            }
            ctor = ctors[json["kind"]]
            del json["kind"]
            return ctor(**json)

        distr = {
            "Delegate": 0.05,
            "Undelegate": 0.05,
            "JumpNBlocks": 0.4,
            "Deliver": 0.4,
            "ProviderSlash": 0.05,
            "ConsumerSlash": 0.05,
        }

        templates = []
        templates.extend(self.candidate_Delegate())
        templates.extend(self.candidate_Undelegate())
        templates.extend(self.candidate_JumpNBlocks())
        templates.extend(self.candidate_Deliver())
        # templates.extend(self.candidate_ProviderSlash())
        # templates.extend(self.candidate_ConsumerSlash())

        possible = [t.__class__.__name__ for t in templates]
        distr = {k: v for k, v in distr.items() if k in possible}
        scale = sum(distr.values())
        distr = {k: v / scale for k, v in distr.items()}
        # Choose a Class
        class_name = random.choices(list(distr.keys()), weights=list(distr.values()))[0]
        templates = [t for t in templates if t.__class__.__name__ == class_name]
        # Choose a class instance
        a = random.choice(templates)
        if class_name == "Delegate":
            self.select_Delegate(a)
        if class_name == "Undelegate":
            self.select_Undelegate(a)
        if class_name == "JumpNBlocks":
            self.select_JumpNBlocks(a)
        if class_name == "Deliver":
            self.select_Deliver(a)
        if class_name == "ProviderSlash":
            self.select_ProviderSlash(a)
        if class_name == "ConsumerSlash":
            self.select_ConsumerSlash(a)
        return a

    def candidate_Delegate(self):
        ret = []
        for i in range(NUM_VALIDATORS):
            if not self.delegated_since_block[i]:
                ret.append(Delegate(i, None))
        return ret

    def candidate_Undelegate(self):
        ret = []
        for i in range(NUM_VALIDATORS):
            if not self.undelegated_since_block[i]:
                ret.append(Undelegate(i, None))
        return ret

    def candidate_JumpNBlocks(self):
        return [JumpNBlocks(None, None, None)]

    def candidate_Deliver(self):
        ret = []
        for c in {P, C}:
            if self.m.has_undelivered(c):
                ret.append(Deliver(c))
        return ret

    def candidate_ProviderSlash(self):
        ret = []
        for i in range(NUM_VALIDATORS):
            jailed = self.jailed | {i: True}
            cnt = sum(not j for _, j in jailed.items())
            if MAX_VALIDATORS <= cnt:
                ret.append(ProviderSlash(i, None, None, None))
        return ret

    def candidate_ConsumerSlash(self):
        ret = []
        for i in range(NUM_VALIDATORS):
            jailed = self.jailed | {i: True}
            cnt = sum(not j for _, j in jailed.items())
            if MAX_VALIDATORS <= cnt:
                ret.append(ConsumerSlash(i, None, None, None))
        return ret

    def select_Delegate(self, a):
        self.delegated_since_block[a.val] = True
        a.amt = random.randint(1, 5)

    def select_Undelegate(self, a):
        self.undelegated_since_block[a.val] = True
        a.amt = random.randint(1, 5)

    def select_JumpNBlocks(self, a):
        a.chains = random.choice([[P, C], [P], [C]])
        a.n = random.choice([1, 4, 6])
        a.seconds_per_block = 1
        if P in a.chains:
            self.delegated_since_block = {i: False for i in range(NUM_VALIDATORS)}
            self.undelegated_since_block = {i: False for i in range(NUM_VALIDATORS)}

    def select_Deliver(self, a):
        return

    def select_ProviderSlash(self, a):
        self.jailed[a.val] = True
        a.power = random.randint(1, 6)
        a.height = int((random.randint(0, 4) / 4) * self.m.h[P])
        a.factor = SLASH_FACTOR_DOWNTIME

    def select_ConsumerSlash(self, a):
        self.jailed[a.val] = True
        a.power = random.randint(1, 6)
        a.height = int((random.randint(0, 4) / 4) * self.m.h[C])
        a.is_downtime = bool(random.getrandbits(1))


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
        }

    def write(self, fn):
        with open(fn, "w") as fd:
            obj = self.json()
            fd.write(json.dumps(obj, indent=2))


class Driver:
    def __init__(self, model, trace):
        self.m = model
        self.trace = trace

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
        shaper = Shaper(model)
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
