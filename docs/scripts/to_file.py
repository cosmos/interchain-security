from pprint import pprint
# text = [
#     {
#         "sidebar_position": 6,
#         "title": "Frequently Asked Questions",
#         "text": "faq.md",
#     }
# ]

prep = []



with open('faq.md', 'r') as f:
    title = ""
    text = ""
    for line in f:
        # print(line)
        if line.startswith("##"):
            if title:
                prep.append({"title": title, "text": text})
            title = line[3:].strip()
            text = ""
        else:
            text += line
    prep.append({"title": title, "text": text})

for (i, p) in zip(range(1, len(prep)+1), prep):
    name = p["title"].lower().replace(" ", "-").replace("?", "").replace("'", "")
    title = f"{name}.md"
    with open(title, "w") as f:
        f.write(f"""---
sidebar_position: {i}
---\n\n""")
        f.write(f"## {p['title']}\n\n")
        f.write(p["text"])

# pprint(prep)
