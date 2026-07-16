import json

with open('doc/html/js/data.js', 'r') as f:
    content = f.read()

json_str = content[content.find('{'):]
if json_str.endswith(';\n'):
    json_str = json_str[:-2]
elif json_str.endswith(';'):
    json_str = json_str[:-1]

data = json.loads(json_str)
print(f"Final valid papers count: {len(data['papers'])}")
