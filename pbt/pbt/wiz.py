import json


def transform(o):
    return [o]


def wiz():
    fp = "traces_subset/trace_1388.json"
    obj = None
    with open(fp, "r") as fd:
        obj = json.loads(fd.read())
    obj = transform(obj)
    fp = "traces_subset/trace_0000.json"
    with open(fp, "w") as fd:
        fd.write(json.dumps(obj, indent=2))
