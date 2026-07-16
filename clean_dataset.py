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

for paper_id, paper in data['papers'].items():
    title = paper.get('title', '')
    authors = paper.get('authors', [])
    
    # Identify junk
    if 'Unknown Author' in authors or title.startswith('paper_') or title == '2309.09171v1':
        keys_to_remove.append(paper_id)

for k in keys_to_remove:
    del data['papers'][k]

print(f"Removed {len(keys_to_remove)} junk papers. Remaining: {len(data['papers'])}.")

with open('doc/html/js/data.js', 'w') as f:
    f.write(prefix + json.dumps(data, indent=2) + suffix)

