import json


def blocks(bs):
    bs = {int(k): v for k, v in bs.items()}
    keys = sorted(list(bs.keys()))
    assert [i == x for i, x in enumerate(keys)]
    return [bs[i] for i in range(len(keys))]


def transform(o):
    return [
        {
            "actions": o["actions"],
            "events": o["events"]["events"],
            "blocks": {
                "provider": blocks(o["blocks"]["blocks"]["provider"]),
                "consumer": blocks(o["blocks"]["blocks"]["consumer"]),
            },
        }
    ]


def wiz():
    fp = "traces_subset/trace_1388.json"
    obj = None
    with open(fp, "r") as fd:
        obj = json.loads(fd.read())
    obj = transform(obj)
    fp = "traces_subset/trace_0000.json"
    with open(fp, "w") as fd:
        fd.write(json.dumps(obj, indent=2))
