import json

with open('doc/html/js/data.js', 'r') as f:
    content = f.read()

prefix = 'window.DH_DATA = '
suffix_found = False
json_str = content[content.find('{'):]
if json_str.endswith(';\n'):
    json_str = json_str[:-2]
    suffix = ';\n'
elif json_str.endswith(';'):
    json_str = json_str[:-1]
    suffix = ';'
else:
    suffix = ''

data = json.loads(json_str)

initial_count = len(data['papers'])
keys_to_remove = []

fake_keywords = ['team', 'group', 'researchers', 'various', 'unknown']

for paper_id, paper in data['papers'].items():
    authors = paper.get('authors', [])
    is_fake = False
    for a in authors:
        a_lower = a.lower()
        if any(kw in a_lower for kw in fake_keywords):
            is_fake = True
            break
    if is_fake:
        keys_to_remove.append(paper_id)

for k in keys_to_remove:
    del data['papers'][k]

# Also clean authors dict
for k in list(data['authors'].keys()):
    if any(kw in k.lower() for kw in fake_keywords):
        del data['authors'][k]
    else:
        # filter their papers list
        data['authors'][k]['papers'] = [p for p in data['authors'][k]['papers'] if p not in keys_to_remove]

# clean concepts papers list
for k in list(data['concepts'].keys()):
    data['concepts'][k]['papers'] = [p for p in data['concepts'][k]['papers'] if p not in keys_to_remove]

print(f"Removed {len(keys_to_remove)} junk papers. Remaining: {len(data['papers'])}.")

with open('doc/html/js/data.js', 'w') as f:
    f.write(prefix + json.dumps(data, indent=2) + suffix)

