import json

with open('doc/html/js/data.js', 'r') as f:
    content = f.read()

json_str = content[content.find('{'):]
if json_str.endswith(';\n'):
    json_str = json_str[:-2]
elif json_str.endswith(';'):
    json_str = json_str[:-1]

data = json.loads(json_str)
for paper_id, paper in data['papers'].items():
    if 'Unknown Author' in paper.get('authors', []) or paper.get('title', '').startswith('paper_') or paper.get('title') == '2309.09171v1':
        print(f"ID: {paper_id}, Title: {paper.get('title')}")
