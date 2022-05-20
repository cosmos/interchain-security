from .constants import *
from recordclass import recordclass
import random

Delegate = recordclass("Delegate", ["val", "amt"])
Undelegate = recordclass("Undelegate", ["val", "amt"])
JumpNBlocks = recordclass("JumpNBlocks", ["chains", "n", "seconds_per_block"])
Deliver = recordclass("Deliver", ["chain"])
ProviderSlash = recordclass("ProviderSlash", ["val", "power", "height", "factor"])
ConsumerSlash = recordclass("ConsumerSlash", ["val", "power", "height", "is_downtime"])


def action_from_json(obj):
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
    ctor = ctors[obj["kind"]]
    del obj["kind"]
    return ctor(**obj)


class Shaper:
    """
    Used to put further constrains on which actions are valid,
    and modify actions to make them valid.
    """

    def __init__(self, model):
        self.m = model
        self.delegated_since_block = {i: False for i in range(NUM_VALIDATORS)}
        self.undelegated_since_block = {i: False for i in range(NUM_VALIDATORS)}
        self.jailed = {i: False for i in range(NUM_VALIDATORS)}

    def action(self):
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
