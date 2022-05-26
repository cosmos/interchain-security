from os import listdir
from os.path import isfile, join
import json


def combine(dir, fnout):

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


def foo():
    combine("traces_covering/", "traces_covering")
    combine("traces_diverse/", "traces_diverse")
