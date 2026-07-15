import json
import os

html_dir = "/Users/xavierfresquet/Documents/Musicologie/CAPTAL-LAB/4-MISC/math/riemann/doc/html"
corpus_path = os.path.join(html_dir, "rh_corpus_database.json")
kg_path = os.path.join(html_dir, "knowledge_graphs.json")
out_path = os.path.join(html_dir, "js", "data.js")

with open(corpus_path, "r") as f:
    corpus_data = json.load(f)

with open(kg_path, "r") as f:
    kg_data = json.load(f)

js_content = f"""// Auto-generated data bundle to allow offline viewing via file:///
window.DH_DATA = {{
    corpus: {json.dumps(corpus_data)},
    knowledgeGraphs: {json.dumps(kg_data)}
}};
"""

with open(out_path, "w") as f:
    f.write(js_content)

print("Data bundled successfully to js/data.js")
