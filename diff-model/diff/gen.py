from collections import Counter
import random
import sys
import shutil
import os
import time
import json
from .model import Model
from .constants import *
from .properties import *
from .constants import *
from .blocks import *
from recordclass import asdict, recordclass
from .events import *

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
            "Delegate": 0.06,
            "Undelegate": 0.06,
            "JumpNBlocks": 0.42,
            "Deliver": 0.42,
            "ProviderSlash": 0.02,
            "ConsumerSlash": 0.02,
        }

        templates = []
        templates.extend(self.candidate_Delegate())
        templates.extend(self.candidate_Undelegate())
        templates.extend(self.candidate_JumpNBlocks())
        templates.extend(self.candidate_Deliver())
        templates.extend(self.candidate_ProviderSlash())
        templates.extend(self.candidate_ConsumerSlash())

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
        a.amt = random.randint(1, 5) * 1000

    def select_Undelegate(self, a):
        self.undelegated_since_block[a.val] = True
        a.amt = random.randint(1, 4) * 1000

    def select_JumpNBlocks(self, a):
        a.chains = random.choice([[P, C], [P], [C]])
        a.n = random.choice([1, 4, 7])
        a.seconds_per_block = 1
        if P in a.chains:
            self.delegated_since_block = {i: False for i in range(NUM_VALIDATORS)}
            self.undelegated_since_block = {i: False for i in range(NUM_VALIDATORS)}

    def select_Deliver(self, a):
        return

    def select_ProviderSlash(self, a):
        self.jailed[a.val] = True
        a.power = random.randint(1, 6) * 1000
        a.height = int((random.randint(0, 4) / 4) * self.m.h[P])
        a.factor = SLASH_FACTOR_DOWNTIME

    def select_ConsumerSlash(self, a):
        self.jailed[a.val] = True
        a.power = random.randint(1, 6) * 1000
        a.height = int((random.randint(0, 4) / 4) * self.m.h[C])
        a.is_downtime = bool(random.getrandbits(1))


class Trace:
    def __init__(self):
        self.actions = []
        self.consequences = []
        self.blocks = None
        self.events = None

    def add_action(self, action):
        self.actions.append(action)

    def add_consequence(self, snapshot):
        self.consequences.append(snapshot)

    def dump(self, fn):
        def default(obj):
            try:
                return obj.json()
            except AttributeError:
                pass
            try:
                return asdict(obj)
            except TypeError:
                pass
            return vars(obj)

        def to_json():
            def ugly():
                ret = {
                    "actions": [
                        {"kind": e.__class__.__name__} | asdict(e) for e in self.actions
                    ],
                    "consequences": self.consequences,
                    "blocks": self.blocks,
                    "events": self.events,
                }
                return json.loads(json.dumps(ret, indent=2, default=default))

            def pretty(o):
                def blocks(bs):
                    bs = {int(k): v for k, v in bs.items()}
                    keys = sorted(list(bs.keys()))
                    assert [i == x for i, x in enumerate(keys)]
                    return [bs[i] for i in range(len(keys))]

                return [
                    {
                        "actions": o["actions"],
                        "events": o["events"]["events"],
                        "blocks": {
                            "provider": blocks(o["blocks"]["blocks"]["provider"]),
                            "consumer": blocks(o["blocks"]["blocks"]["consumer"]),
                        },
                        "consequences": o["consequences"],
                    }
                ]

            return pretty(ugly())

        with open(fn, "w") as fd:
            fd.write(json.dumps(to_json(), indent=2, default=default))


def do_action(model, a):
    if isinstance(a, Delegate):
        model.delegate(a.val, a.amt)
    if isinstance(a, Undelegate):
        model.undelegate(a.val, a.amt)
    if isinstance(a, JumpNBlocks):
        model.jump_n_blocks(a.n, a.chains, a.seconds_per_block)
    if isinstance(a, Deliver):
        model.deliver(a.chain)
    if isinstance(a, ProviderSlash):
        model.provider_slash(a.val, a.height, a.power, a.factor)
    if isinstance(a, ConsumerSlash):
        model.consumer_slash(a.val, a.power, a.height, a.is_downtime)


def load_debug_actions():
    obj = None
    with open("debug.json", "r") as fd:
        obj = json.loads(fd.read())
    return obj["actions"]


def gen():
    debug = False
    GOAL_TIME_MINS = 5
    NUM_ACTIONS = 40

    shutil.rmtree("traces/")
    os.makedirs("traces/")

    num_runs = 1 if debug else 99999999999  # will be adjusted
    elapsed = 0
    i = 0

    all_events = []

    while i < num_runs:
        i += 1
        if not debug and 10 < elapsed:
            num_runs = (GOAL_TIME_MINS * 60) / (elapsed / i)
        t_start = time.time()

        blocks = Blocks()
        events = Events()
        model = Model(blocks, events)
        shaper = Shaper(model)
        trace = Trace()
        actions = None
        k = NUM_ACTIONS
        if debug:
            actions = [shaper.action(json=a) for a in load_debug_actions()]
            k = len(actions)
        try:
            for j in range(k):
                a = actions[j] if debug else shaper.action()
                trace.add_action(a)
                do_action(model, a)
                trace.add_consequence(model.snapshot())
            # assert staking_without_slashing(blocks)
            # assert bond_based_consumer_voting_power(blocks)
        except Exception:
            trace.blocks = blocks
            trace.events = events
            trace.dump("debug.json")
            sys.exit(1)
        else:
            trace.blocks = blocks
            trace.events = events
            all_events.append(events)
            trace.dump(f"traces/trace_{i}.json")

        t_end = time.time()
        elapsed += t_end - t_start

    cnt = Counter()
    for events in all_events:
        for e in events.events:
            cnt[e] += 1

    total = sum(c for _, c in cnt.most_common())
    stats = {e: cnt[e] for e in Events.Event}
    listed = sorted(list(stats.items()), key=lambda pair: pair[1], reverse=True)
    for e, c in listed:
        print(e, f"{c},({round(c/total, 8)})")

    print(f"Ran {i} runs")
