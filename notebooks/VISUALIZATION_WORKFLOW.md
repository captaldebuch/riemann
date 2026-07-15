# Data Visualization Workflow: Complete Guide
## From Papers to Interactive Dashboards

This guide explains the complete pipeline for parsing mathematical papers, building the structured database, and generating interactive visualizations for the website.

---

## 1. OVERVIEW: The Pipeline

```
PDF Papers (30)
    ↓
Marker/GROBID (PDF → Markdown)
    ↓
Claude API + Instructor (Extract structured data)
    ↓
Pydantic Validation (Enforce schema)
    ↓
JSON Database (Human-readable) + SQLite (Queryable)
    ↓
NetworkX/Altair/Plotly (Generate visualizations)
    ↓
HTML Artifacts (Embed in website)
    ↓
Website Display (visualizations.html)
```

---

## 2. FOLDER STRUCTURE

```
riemann/
├── papers/                          # Source PDFs
│   ├── 1111.0931.pdf
│   ├── 1601.06839.pdf
│   └── ... (30 papers total)
│
├── notebooks/
│   ├── 01_parse_and_visualize.ipynb    # Main parser
│   ├── SCHEMA_MATHLIT_DATABASE.md      # Database schema definition
│   └── VISUALIZATION_WORKFLOW.md       # This file
│
├── doc/html/
│   ├── visualizations.html              # Visualization hub page
│   ├── corpus.html                      # Paper collection page
│   └── visualizations/                  # Generated output folder
│       ├── citation_network.html
│       ├── lean_dependency_dag.svg
│       ├── timeline_domain.html
│       └── semantic_clusters.html
│
└── rh_corpus_database.json             # Exported database (root)
```

---

## 3. STEP-BY-STEP WORKFLOW

### Phase 1: Prepare Your Environment

```bash
cd /Users/xavierfresquet/Documents/Musicologie/CAPTAL-LAB/4-MISC/math/riemann

# Create visualizations folder
mkdir -p doc/html/visualizations

# Install dependencies
pip install marker-pdf pydantic instructor networkx pyvis altair plotly scikit-learn umap-learn
```

### Phase 2: Run the Parser Notebook

Open `notebooks/01_parse_and_visualize.ipynb` in Jupyter:

```bash
jupyter notebook notebooks/01_parse_and_visualize.ipynb
```

**What happens in the notebook:**

1. **Setup cell:** Defines paths and imports Pydantic schema
2. **Schema definition:** Loads all model classes (ArticleReference, Theorem, Intuition, etc.)
3. **Data loading:** Reads sample database OR parses PDFs using Marker + Claude API
4. **VIZ 1 - Citation Network:** Builds NetworkX graph, exports to Pyvis HTML
5. **VIZ 2 - Lean DAG:** Creates Graphviz dependency diagram
6. **VIZ 3 - Timeline:** Generates Altair interactive scatter plot
7. **VIZ 4 - Semantic Clusters:** Computes t-SNE embeddings, exports Plotly scatter
8. **Export:** Saves JSON database and all visualizations

### Phase 3: Generate Full Database (Production Mode)

For parsing all 30 papers with Claude API:

```python
# In notebook cell (replace sample data with actual parsing):
from marker.converter import convert_pdf_to_markdown
from instructor import Instructor
from anthropic import Anthropic

client = Anthropic()
papers_dir = Path("../papers")

articles = []
for pdf_path in papers_dir.glob("*.pdf"):
    # Convert PDF to markdown
    markdown, metadata = convert_pdf_to_markdown(str(pdf_path))
    
    # Parse with Claude + Instructor
    response = client.messages.create(
        model="claude-opus-4-8",
        max_tokens=2000,
        system="Extract structured mathematical metadata from academic paper...",
        messages=[{"role": "user", "content": markdown}]
    )
    
    # Validate with Pydantic
    article = ArticleReference(**response.parsed)
    articles.append(article)

# Then continue with rest of notebook to generate visualizations
```

### Phase 4: Deploy to Website

```bash
# Copy generated visualizations to website folder
cp visualizations/* /Users/xavierfresquet/Documents/Musicologie/CAPTAL-LAB/4-MISC/math/riemann/doc/html/visualizations/

# Copy database for reference
cp rh_corpus_database.json /Users/xavierfresquet/Documents/Musicologie/CAPTAL-LAB/4-MISC/math/riemann/doc/html/
```

Then open `/doc/html/visualizations.html` in browser to see the complete dashboard.

---

## 4. CUSTOMIZING THE VISUALIZATIONS

### Adding Custom Paper Metadata

Edit the sample data in the notebook before generating visualizations:

```python
sample_database = {
    "articles": [
        {
            "id": "arxiv:NEW_PAPER_ID",
            "title": "Paper Title",
            "authors": [{"name": "Author Name"}],
            "year": 2024,
            "role_in_project": "H15",      # Change this: H13, H14, H15, Phase_NB
            "relevance_score": 0.85,        # 0.0 to 1.0
            "tags": ["new-tag", "technique"],
            ...
        }
    ],
    ...
}
```

### Customizing Node Colors in Citation Network

In the "VIZ 1" cell of the notebook:

```python
role_colors = {
    "H13": "#10b981",      # green
    "H14": "#3b82f6",      # blue
    "H15": "#ef4444",      # red
    "Phase_NB": "#f59e0b", # amber
    "Spectral": "#8b5cf6",  # purple (add new roles)
    "General": "#6b7280"   # gray
}
```

### Customizing Timeline Domains

Edit the "VIZ 3" cell to group papers differently:

```python
# Instead of role_in_project, use mathematical domain:
timeline_data.append({
    'Year': article.year,
    'Domain': 'Spectral Theory',  # Replace role with domain
    ...
})
```

### Customizing Semantic Clustering

To use different text sources for embeddings:

```python
# Instead of intuitions, use key math insights:
concept_texts = [
    f"{insight.main_contribution}. {'. '.join([t.description for t in insight.key_techniques])}"
    for insight in db.insights
]
```

---

## 5. DATABASE SCHEMA: Quick Reference

### ArticleReference
```python
{
    "id": "arxiv:XXXX.XXXXX",          # unique identifier
    "title": str,
    "authors": [{"name": str}],
    "year": int,
    "role_in_project": "H13|H14|H15|Phase_NB",
    "relevance_score": 0.0-1.0,
    "tags": ["tag1", "tag2"]
}
```

### KeyInsights
```python
{
    "article_id": "arxiv:XXXX.XXXXX",
    "main_theorem": {
        "label": "Theorem 1.1",
        "statement": "...",
        "proof_sketch": "...",
        "assumptions": [...]
    },
    "key_techniques": [
        {"name": "...", "description": "..."}
    ],
    "mathematical_objects": [
        {"name": "...", "category": "...", ...}
    ]
}
```

### FormalizationPotential
```python
{
    "article_id": "arxiv:XXXX.XXXXX",
    "overall_readiness": 0.6,              # 0.0-1.0
    "formalizable_theorems": ["Thm 1.1"],
    "mathlib_dependencies": [
        {
            "concept": "period-functions",
            "status": "custom-dependency|available-in-mathlib",
            "estimated_effort": "easy|medium|hard"
        }
    ],
    "estimated_weeks": 3.5
}
```

### Connection
```python
{
    "source_id": "arxiv:XXXX.XXXXX",
    "target_id": "arxiv:YYYY.YYYYY",
    "relationship": "extends-method|uses-result-from|inspired-by|...",
    "description": "How they're connected",
    "strength": 0.0-1.0
}
```

---

## 6. ADVANCED FEATURES

### Exporting to SQLite for Querying

In the notebook, after generating JSON database:

```python
import sqlite3
import json

# Load JSON
with open('rh_corpus_database.json') as f:
    db_json = json.load(f)

# Create SQLite
conn = sqlite3.connect('rh_corpus_database.db')
cursor = conn.cursor()

# Create tables
cursor.execute('''
    CREATE TABLE articles (
        id TEXT PRIMARY KEY,
        title TEXT,
        authors JSON,
        year INT,
        role_in_project TEXT,
        relevance_score REAL
    )
''')

# Insert data
for article in db_json['articles']:
    cursor.execute(
        'INSERT INTO articles VALUES (?, ?, ?, ?, ?, ?)',
        (
            article['id'],
            article['title'],
            json.dumps(article['authors']),
            article['year'],
            article['role_in_project'],
            article['relevance_score']
        )
    )

conn.commit()
conn.close()
```

Then query:

```sql
-- Find all H15-relevant papers
SELECT title, year FROM articles WHERE role_in_project = 'H15' ORDER BY year DESC;

-- Find most recent papers in each role
SELECT role_in_project, MAX(year) FROM articles GROUP BY role_in_project;
```

### Building a Custom Web Dashboard

To create a filterable, searchable dashboard in HTML/JavaScript:

```html
<!-- In visualizations.html or new dashboard.html -->
<input type="text" id="search-box" placeholder="Search papers...">
<select id="role-filter">
    <option value="">All Roles</option>
    <option value="H13">H13</option>
    <option value="H14">H14</option>
    <option value="H15">H15</option>
</select>

<script>
fetch('rh_corpus_database.json')
  .then(r => r.json())
  .then(db => {
    let papers = db.articles;
    
    // Filter by search
    const searchBox = document.getElementById('search-box');
    searchBox.addEventListener('input', (e) => {
        const query = e.target.value.toLowerCase();
        const filtered = papers.filter(p => 
            p.title.toLowerCase().includes(query) ||
            p.authors.some(a => a.name.toLowerCase().includes(query))
        );
        renderTable(filtered);
    });
    
    // Filter by role
    const roleFilter = document.getElementById('role-filter');
    roleFilter.addEventListener('change', (e) => {
        const role = e.target.value;
        const filtered = role ? papers.filter(p => p.role_in_project === role) : papers;
        renderTable(filtered);
    });
  });
</script>
```

### Semantic Search via Embeddings

To add semantic search (find "conceptually similar" papers):

```python
from openai import OpenAI
import numpy as np

client = OpenAI()

# Generate embeddings for all intuition texts
embeddings = {}
for intuition in db.intuitions:
    text = " ".join([i.description for i in intuition.author_intuitions])
    response = client.embeddings.create(
        model="text-embedding-3-small",
        input=text
    )
    embeddings[intuition.article_id] = response.data[0].embedding

# Search: find papers similar to a query
query = "Möbius function cancellation in weighted sums"
query_embedding = client.embeddings.create(
    model="text-embedding-3-small",
    input=query
).data[0].embedding

# Compute cosine similarity
similarities = {}
for paper_id, embedding in embeddings.items():
    sim = np.dot(query_embedding, embedding) / (np.linalg.norm(query_embedding) * np.linalg.norm(embedding))
    similarities[paper_id] = sim

# Sort and display
sorted_papers = sorted(similarities.items(), key=lambda x: x[1], reverse=True)
for paper_id, score in sorted_papers[:5]:
    print(f"{paper_id}: {score:.3f}")
```

---

## 7. TROUBLESHOOTING

### Problem: "No module named 'marker'"
**Solution:** Install with `pip install marker-pdf`

### Problem: Visualization HTML files are blank
**Solution:** Ensure the notebook runs successfully and generates output files in `./visualizations/` before copying to website

### Problem: Citation network shows no edges
**Solution:** Check that `db.connections` list is populated. If using sample data, edges are already included.

### Problem: t-SNE semantic clusters gives "perplexity error"
**Solution:** This occurs if fewer than 5 papers have intuitions. Either add more intuitions or use:
```python
tsne = TSNE(n_components=2, perplexity=min(5, len(X)-1))  # Already in notebook
```

### Problem: Large database causes Pyvis graph to load slowly
**Solution:** Filter edges before creating network:
```python
# Keep only strong connections
strong_connections = [c for c in db.connections if c.strength > 0.6]
for conn in strong_connections:
    G.add_edge(conn.source_id, conn.target_id)
```

---

## 8. MAINTENANCE & UPDATES

### Monthly Maintenance Checklist

- [ ] **Add new papers:** Add PDFs to `papers/` folder
- [ ] **Update corpus:** Run notebook to parse new papers
- [ ] **Validate database:** Check `rh_corpus_database.json` for consistency
- [ ] **Regenerate visualizations:** Run all visualization cells
- [ ] **Deploy to website:** Copy files to `doc/html/visualizations/`
- [ ] **Test in browser:** Open `visualizations.html` and verify all four visualizations load

### Updating the Schema

If you need to add new fields to papers (e.g., a new mathematical technique):

1. Edit `SCHEMA_MATHLIT_DATABASE.md` to add the field
2. Update the Pydantic model in the notebook
3. Update the Claude prompt to extract the new field
4. Re-run the notebook to parse papers with the new field
5. Update visualization cells if the new field affects any charts

---

## 9. EXAMPLE: Adding a New Visualization

To add a **"Author Network"** visualization (papers grouped by shared authors):

```python
# In the notebook, after VIZ 4, add:

# VIZ 5: Author Collaboration Network
author_graph = nx.Graph()  # Undirected (collaborations are symmetric)

# Add authors as nodes, papers as connections
for article in db.articles:
    for i, author1 in enumerate(article.authors):
        for author2 in article.authors[i+1:]:
            author_graph.add_edge(author1.name, author2.name, weight=1)

# Create Pyvis
net = Network(height="750px", width="100%", directed=False)
net.from_nx(author_graph)
net.show(str(VIZ_OUTPUT / "author_network.html"))
```

Then add to `visualizations.html`:

```html
<div class="viz-card">
    <div class="viz-header" style="background: linear-gradient(135deg, #fa709a 0%, #fee140 100%);">
        <div class="viz-icon">👥</div>
        <div class="viz-title">
            <h2>Author Collaboration Network</h2>
        </div>
    </div>
    <div class="viz-body">
        <iframe src="visualizations/author_network.html" class="viz-embed"></iframe>
    </div>
</div>
```

---

## 10. RESOURCES & LINKS

- **Pydantic documentation:** https://docs.pydantic.dev/
- **Marker (PDF extraction):** https://github.com/VikParuchuri/marker
- **NetworkX (graph analysis):** https://networkx.org/
- **Pyvis (graph visualization):** https://pyvis.readthedocs.io/
- **Altair (interactive charts):** https://altair-viz.github.io/
- **Plotly (JavaScript charts):** https://plotly.com/python/
- **t-SNE/UMAP (embeddings):** https://umap-learn.readthedocs.io/

---

## 11. QUICK START (TL;DR)

```bash
# 1. Navigate to repo
cd /Users/xavierfresquet/Documents/Musicologie/CAPTAL-LAB/4-MISC/math/riemann

# 2. Install dependencies
pip install marker-pdf pydantic instructor networkx pyvis altair plotly scikit-learn umap-learn

# 3. Run notebook
jupyter notebook notebooks/01_parse_and_visualize.ipynb

# 4. Execute all cells (takes ~5 minutes)

# 5. Copy outputs to website
cp visualizations/* doc/html/visualizations/

# 6. Open in browser
open doc/html/visualizations.html
```

---

**Last Updated:** 2026-07-15  
**Maintainer:** scai@sorbonne-universite.fr
