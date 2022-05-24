import os
import shutil
import json
import random
import functools
from os import listdir
from os.path import isfile, join

"""
Dirty prototype of trace selection algorithm

Algorithm:

Input: a set of n traces and a projection algorithm mapping a trace to a set of some type 
Output: a set of m pairwise unique traces minimizing a loss function with m < n

Pseudocode:
    Sample a population G of m traces uniformly from the search space (the set of all possible valid sets of size m)
    Repeat as desired:
        Choose sx, sy from G
        sx', sy' = crossover(sx, sy, p)
        sx'' = mutate(sx')
        sy'' = mutate(sy')
        if valid(sx'') and valid(sy'') /\ min(loss(sx''),loss(sy'')) <= min(loss(sx), loss(sy)):
            sx := sx''
            sy := sy''
    Choose best and return the best set of traces from G according to loss

loss(s: set of m traces) = sum(similiarity(ti,tj)) for ti,tj in s, i#j

similarity(ti, tj) = cardinality(project(ti) intersect project(tj))/cardinality(project(ti) union project(tj))
"""


PARAM_population_size = 50
PARAM_target_size = 64
PARAM_crossover_probability = 0.75
PARAM_iterations = 160000


def select_subset(
    list_of_sets, *, target_size=PARAM_target_size, iterations=PARAM_iterations
):

    N = len(list_of_sets)

    def crossover(vx, vy):
        vx, vy = list(vx), list(vy)
        n = len(vx)
        assert len(vy) == n
        r = random.choice(range(1, n - 1))
        for i in range(r, n):
            vx[i], vy[i] = vy[i], vx[i]
        return vx, vy

    def mutate(v):
        v = list(v)
        n = len(v)
        P = 1 / n
        for i in range(n):
            if random.uniform(0, 1) < P:
                v[i] = random.choice(range(N))
        return v

    def valid(v):
        return len(set(v)) == len(v)

    @functools.cache
    def similarity_f(i, j):
        A = list_of_sets[i]
        B = list_of_sets[j]
        intersect = A.intersection(B)
        union = A.union(B)
        assert 0 < len(union), (A, B)
        return round(len(intersect) / len(union), 3)

    def loss(v):
        x = 0
        for i in range(len(v) - 1):
            for j in range(i + 1, len(v)):
                x += similarity_f(v[i], v[j])
        return x

    # Initialize population
    G = [None] * PARAM_population_size
    G_ixs = list(range(len(G)))
    for i in G_ixs:
        G[i] = random.sample(range(N), target_size)

    def best():
        best_ix = 0
        best_loss = loss(G[0])
        for i in range(1, len(G)):
            value = loss(G[i])
            if value < best_loss:
                best_ix = i
                best_loss = value
        return G[best_ix], best_loss

    _, random_choice_loss = best()

    for k in range(iterations):
        if k % 1000 == 0:
            print(f"Iter {k}")
        sxi, syi = random.sample(G_ixs, 2)
        sx = list(G[sxi])
        sy = list(G[syi])
        if random.uniform(0, 1) < PARAM_crossover_probability:
            sx, sy = crossover(sx, sy)
        sx = mutate(sx)
        sy = mutate(sy)
        if valid(sx) and valid(sy):
            if min(loss(sx), loss(sy)) <= min(loss(G[sxi]), loss(G[syi])):
                G[sxi] = sx
                G[syi] = sy

    indexes_of_best_sets, loss_value = best()
    return indexes_of_best_sets, loss_value, random_choice_loss


def mapper(obj):
    return set(obj["events"]["events"])


def bar():
    PATH = "traces/"
    files = [f for f in listdir(PATH) if isfile(join(PATH, f))]
    print(files[:5])

    mapped = {}
    event_names = set()

    for fn in files:
        fp = join(PATH, fn)
        obj = None
        with open(fp, "r") as fd:
            obj = json.loads(fd.read())
        mapped[fn] = mapper(obj)
        for en in mapped[fn]:
            event_names.add(en)

    event_names = list(event_names)
    reverse = {en: i for i, en in enumerate(event_names)}

    for k in mapped:
        mapped[k] = set(reverse[en] for en in mapped[k])

    for s in mapped.values():
        # Add the 'empty' event
        s.add(-1)
    ordered = list(mapped.items())
    print(ordered[:5])
    indexes, loss, random_loss = select_subset(
        [pair[1] for pair in ordered], target_size=64, iterations=100000
    )
    print(indexes, loss, random_loss, round(loss / random_loss, 5))

    PATH = "traces_subset/"
    shutil.rmtree(PATH)
    os.makedirs(PATH)
    for i in indexes:
        fn = ordered[i][0]
        with open(join("traces/", fn), "r") as fd_r:
            obj = json.loads(fd_r.read())
            with open(join(PATH, fn), "w") as fd_w:
                fd_w.write(json.dumps(obj, indent=2))
