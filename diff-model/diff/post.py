import json
import os
import shutil
import sys
from collections import Counter
from os import listdir
from os.path import isfile, join
from .events import Events


def greedy_min_cover(vectors):
    target = 10
    hit = [0] * len(vectors[0][1])

    def q(v, h):
        return sum(1 for i, hits in enumerate(v) if hits and h[i] < target)

    ret = []
    while any(x < target for x in hit):
        vectors.sort(key=lambda v: q(v[1], hit), reverse=True)
        v = vectors[0]
        ret.append(v[0])
        vectors = vectors[1:]
        for i, hits in enumerate(v[1]):
            if hits:
                hit[i] += 1

    return ret


def select():
    PATH = "traces/"
    files = [f for f in listdir(PATH) if isfile(join(PATH, f))]
    print(files[:5])

    mapped = {}
    event_names = []
    event_cnt = Counter()

    vectors = []

    for fn in files:
        fp = join(PATH, fn)
        obj = None
        with open(fp, "r") as fd:
            obj = json.loads(fd.read())
        mapped[fn] = set(obj[0]["events"])
        for en in mapped[fn]:
            if en not in set(event_names):
                event_names.append(en)
            event_cnt[en] += 1
        v = [False] * len(list(Events.Event))
        reverse = {en: i for i, en in enumerate(event_names)}
        for en in mapped[fn]:
            v[reverse[en]] = True
        vectors.append((fn, v))

    print("Finished reading traces")

    print("Num events: ", len(event_cnt))
    for e, c in event_cnt.most_common():
        print(e, c, c / len(files))
    print()

    PATH = "traces_covering/"
    shutil.rmtree(PATH, ignore_errors=True)
    os.makedirs(PATH)
    heuristic_covering = greedy_min_cover(vectors)
    print(f"len covering: {len(heuristic_covering)}")
    for fn in heuristic_covering:
        with open(join("traces/", fn), "r") as fd_r:
            obj = json.loads(fd_r.read())
            with open(join(PATH, fn), "w") as fd_w:
                fd_w.write(json.dumps(obj, indent=2))

    sys.exit(1)


def combine():
    def do(dir, fnout):

        PATH = dir
        files = [f for f in listdir(PATH) if isfile(join(PATH, f))]

        ret = []
        for fn in files:
            fp = join(PATH, fn)
            obj = None
            with open(fp, "r") as fd:
                obj = json.loads(fd.read())
            ret.extend(obj)

        with open(f"{fnout}.json", "w") as fd:
            fd.write(json.dumps(ret, indent=2))

    do("traces_covering/", "traces_covering")


def foobar():
    def do(dir):

        # PATH = dir
        # files = [f for f in listdir(PATH) if isfile(join(PATH, f))]
        PATH = ""
        files = ["traces_covering.json"]

        events = set()
        for fn in files:
            fp = join(PATH, fn)
            obj = None
            with open(fp, "r") as fd:
                obj = json.loads(fd.read())
            events.update(obj[0]["events"])

        print(len(events))
        for e in events:
            print(e)

    do("traces_covering/")
