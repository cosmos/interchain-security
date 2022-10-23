with open("debug.log") as fd:
    txt = fd.read()

lines = []
txt = txt.split("\n")
for line in txt:
    s = "action"
    if s in line:
        ix = line.index(s)
        comma = line.index(",", ix)
        first = ix + len(s)
        word = line[first:comma]
        print(word)
        num = int(word)
        s = "diagnostic]"
        ix = line.index(s) + len(s)
        line = line[ix:]
        lines.append((num, line))

lines.sort(key=lambda l: l[0])
for l in lines:
    print(l)
