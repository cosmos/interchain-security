from copy import deepcopy


class Snapshot:
    def __init__(self, model):
        self.T = model.t
        self.h = model.h
        self.t = model.t
        self.outbox_p = model.outbox_p
        self.outbox_c = model.outbox_c


def snapshot(model):
    d = vars(model)
    del d["blocks"]
    return deepcopy(model)
