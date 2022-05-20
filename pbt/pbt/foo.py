from os import listdir
from os.path import isfile, join
import json
import shutil, os

def interesting(obj):
    return True


def foo():
    shutil.rmtree("interesting/")
    os.makedirs("interesting/")
    for fn in [f for f in listdir("traces") if isfile(join("traces", f))]:
        obj = None
        fp = join("traces", fn)
        with open(fp, "r") as fd:
            obj = json.loads(fd.read())
        fp = join("interesting", fn)
        if interesting(obj):
            with open(fp, "w") as fd:
                fd.write(json.dumps(obj, indent=2))
