import json

PREFIX_DRIVER = "/Users/danwt/Documents/work/interchain-security/tests/difference/consumerStuttering/driver/"
PREFIX_TRACE_OUPUTS = "/Users/danwt/Documents/work/interchain-security/tests/difference/consumerStuttering/model/_apalache-out/main.tla/"
DIR = "2022-09-06T17-55-50_14502121096210630182"
js = []
for i in range(10):
    fn = f"{PREFIX_TRACE_OUPUTS}{DIR}/example{i+1}.itf.json"
    with open(fn, 'r') as fd:
        content = fd.read()
        j = json.loads(content)
        js.append(j)

fn = f"{PREFIX_DRIVER}traces.json"
with open(fn, 'w') as fd:
    fd.write(json.dumps(js, indent=2))
