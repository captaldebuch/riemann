# RH Corpus Visualization System
## Complete Guide to Data-Driven Literature Analysis

---

## 🎯 What This System Does

This is a **complete pipeline for transforming mathematical papers into interactive, multi-dimensional data visualizations**. It turns a collection of PDFs into a structured, queryable knowledge base with four distinct perspectives on the corpus:

1. **Citation & Connection Network** — See how papers influence each other
2. **Lean Formalization Roadmap** — Understand proof prerequisites for formal verification
3. **Chronological Timeline** — Track mathematical evolution across domains and time
4. **Semantic Concept Clusters** — Discover hidden connections via mathematical intuition

---

## 📦 Components

### 1. Pydantic Schema (`SCHEMA_MATHLIT_DATABASE.md`)
Defines the complete data structure for mathematical papers:
- **ArticleReference:** Bibliographic metadata + project role
- **KeyInsights:** Main theorems, techniques, mathematical objects
- **Intuitions:** Heuristic arguments, analogies, physical pictures
- **FormalizationPotential:** Lean dependencies, Mathlib gaps, effort estimates
- **Connections:** Directed graph of paper relationships

### 2. Parser Notebook (`01_parse_and_visualize.ipynb`)
Jupyter notebook that:
- Loads or parses PDFs (via Marker/GROBID)
- Extracts structured data (via Claude API + Instructor)
- Validates against Pydantic schema
- Generates all four visualizations
- Exports to JSON database + SQLite

### 3. Visualization Hub (`visualizations.html`)
Professional, responsive website page showcasing:
- All four interactive visualizations
- Database statistics
- Visual encoding explanations
- Links to extend/customize

### 4. Workflow Guide (`VISUALIZATION_WORKFLOW.md`)
Complete step-by-step instructions:
- Environment setup
- Running the notebook
- Customizing visualizations
- Advanced features (SQLite, semantic search)
- Troubleshooting

---

## 🚀 Quick Start

### Prerequisites
```bash
# Python 3.10+
python3 --version

# Jupyter
pip install jupyter
```

### Installation & Execution
```bash
cd /Users/xavierfresquet/Documents/Musicologie/CAPTAL-LAB/4-MISC/math/riemann

# Install all dependencies
pip install marker-pdf pydantic instructor networkx pyvis altair plotly scikit-learn umap-learn

# Launch Jupyter
jupyter notebook notebooks/01_parse_and_visualize.ipynb

# Run all cells in order (takes ~5 minutes)

# Copy visualizations to website
mkdir -p doc/html/visualizations
cp visualizations/* doc/html/visualizations/

# View in browser
open doc/html/visualizations.html
```

---

## 📊 The Four Visualizations

### 1️⃣ Citation & Connection Network
**File:** `citation_network.html` (interactive, draggable, 750px height)

**What you see:**
- Papers as colored nodes (green=H13, blue=H14, red=H15, amber=Phase NB)
- Edges = mathematical relationships (extends-method, uses-result-from, etc.)
- Node size ∝ number of incoming citations (hubs = influential papers)
- Hover for details; drag to explore; physics simulation for layout

**Use case:**
- Understand paper influence and dependencies
- Find "gateway papers" that bridge different approaches
- Discover clusters of related work

**Example:** Bettin-Conrey (H15) → uses result from → Auli-Bayad-Beck (reciprocity machinery)

---

### 2️⃣ Lean Formalization Dependency DAG
**File:** `lean_dependency_dag.svg` (static, hierarchical diagram)

**What you see:**
- Top: Main theorem to formalize (goal)
- Middle: Prerequisites (other theorems, techniques, mathematical objects)
- Bottom: Foundational axioms and Mathlib
- Solid boxes = already in Mathlib; dashed boxes = must be formalized
- Edges labeled with effort (easy, medium, hard, research-level)

**Use case:**
- Plan formalization work in Lean
- Identify Mathlib gaps blocking progress
- Estimate time to complete a proof
- Break large proofs into manageable pieces

**Example:** To formalize Bettin-Conrey Theorem 1.1, you need period-function machinery (custom, medium effort) which depends on Fourier analysis (in Mathlib).

---

### 3️⃣ Chronological Timeline Matrix
**File:** `timeline_domain.html` (interactive scatter plot, Altair)

**What you see:**
- X-axis: Publication year (1859–2024)
- Y-axis: Mathematical role (H13, H14, H15, Phase NB)
- Bubble color: Formalization difficulty (light=easy, dark=hard)
- Bubble size: Formalization readiness (large=more formalizeable)
- Hover: See full title, authors, readiness score

**Use case:**
- Understand historical evolution of RH approaches
- See which modern papers are most "formalizable"
- Identify foundational vs. recent contributions
- Plan which papers to tackle first for Lean formalization

**Example:** Early works (pre-2000) are classical but harder to formalize; recent works (2015+) are more algorithmic and formalize faster.

---

### 4️⃣ Semantic Concept Clusters
**File:** `semantic_clusters.html` (interactive t-SNE embedding, Plotly)

**What you see:**
- 2D embedding of papers based on mathematical intuitions
- Position = semantic similarity (papers close together share deep heuristic analogies)
- Color = project role (H13, H14, H15, Phase NB)
- Hover: See paper title, role, core intuition

**Use case:**
- Discover papers that should be connected but don't directly cite each other
- Find alternative proof techniques for a given problem
- Understand family resemblances between papers across eras
- Plan literature reviews by conceptual clusters, not chronology

**Example:** A 1970s analytic number theory paper on Dirichlet series and a 2010s quantum chaos paper on random matrices may cluster together because both rely on "spectral spacing heuristics."

---

## 🏗️ Architecture: How It Works

```
┌─────────────────────────────────────────────────────────────┐
│ Input: PDF Papers (30 files, ~500GB total)                  │
└─────────────────────────────────────────────────────────────┘
                            ↓
┌─────────────────────────────────────────────────────────────┐
│ Marker (PDF → Markdown, preserves LaTeX)                    │
└─────────────────────────────────────────────────────────────┘
                            ↓
┌─────────────────────────────────────────────────────────────┐
│ Claude API + Instructor (LLM-powered extraction)            │
│ ├─ Extract article metadata (authors, year, arxiv ID)      │
│ ├─ Identify main theorems and proof sketches               │
│ ├─ Extract key techniques and mathematical objects         │
│ ├─ Capture heuristic arguments and intuitions              │
│ └─ Assess Lean formalization potential                     │
└─────────────────────────────────────────────────────────────┘
                            ↓
┌─────────────────────────────────────────────────────────────┐
│ Pydantic Validation (Type safety, enforce schema)           │
└─────────────────────────────────────────────────────────────┘
                            ↓
┌──────────────────┬────────────────────┬──────────────────┐
│   JSON Export    │   SQLite Export     │ Add Connections  │
│ (human-readable) │ (queryable)         │ (graph edges)    │
└──────────────────┴────────────────────┴──────────────────┘
                            ↓
          ┌─────────────────┼─────────────────┐
          ↓                 ↓                 ↓
    ┌──────────┐     ┌──────────┐    ┌──────────┐
    │NetworkX  │     │Graphviz  │    │Altair    │
    │ + Pyvis  │     │(SVG DAG) │    │(Timeline)│
    └──────────┘     └──────────┘    └──────────┘
          ↓                 ↓                 ↓
    ┌──────────────────────────────────────────────┐
    │              Plotly (t-SNE)                  │
    └──────────────────────────────────────────────┘
          ↓                 ↓                 ↓
    ┌──────────┐     ┌──────────┐    ┌──────────┐
    │ .html    │     │ .svg     │    │ .html    │
    │ (iframe) │     │ (embed)  │    │ (iframe) │
    └──────────┘     └──────────┘    └──────────┘
                            ↓
          ┌───────────────────────────────┐
          │  visualizations.html           │
          │ (Professional hub page)        │
          │ ├─ Citation network            │
          │ ├─ Formalization DAG           │
          │ ├─ Timeline                    │
          │ └─ Semantic clusters           │
          └───────────────────────────────┘
                            ↓
          ┌───────────────────────────────┐
          │    Website Integration         │
          │ doc/html/visualizations.html   │
          └───────────────────────────────┘
```

---

## 🔧 Tech Stack

| Component | Library | Purpose |
|-----------|---------|---------|
| **PDF Extraction** | Marker, GROBID | Convert PDFs to Markdown with LaTeX preserved |
| **LLM Parsing** | Claude API + Instructor | Extract structured data with type safety |
| **Data Validation** | Pydantic | Enforce schema, generate JSON schema |
| **Graph Analysis** | NetworkX | Build and analyze citation network |
| **Graph Visualization** | Pyvis | Interactive, physics-simulated network graph |
| **Dependency DAG** | Graphviz, Pydot | Hierarchical diagram of proof prerequisites |
| **Interactive Charts** | Altair | Declarative visualization grammar |
| **3D Embeddings** | Plotly | Interactive scatter plots |
| **Dimension Reduction** | t-SNE, UMAP | Reduce embeddings to 2D for visualization |
| **Text Embeddings** | OpenAI Embeddings | Semantic similarity computation |
| **Database** | JSON + SQLite | Persistent storage, queryable |

---

## 📖 File Guide

```
riemann/
├── notebooks/
│   ├── 01_parse_and_visualize.ipynb      ← Run this notebook
│   ├── SCHEMA_MATHLIT_DATABASE.md        ← Database schema
│   ├── VISUALIZATION_WORKFLOW.md         ← Detailed instructions
│   └── README_VISUALIZATIONS.md          ← This file
│
├── doc/html/
│   ├── visualizations.html               ← Main visualization hub
│   ├── visualizations/                   ← Generated outputs (after running notebook)
│   │   ├── citation_network.html
│   │   ├── lean_dependency_dag.svg
│   │   ├── timeline_domain.html
│   │   └── semantic_clusters.html
│   ├── index.html                        ← Link to visualizations
│   ├── corpus.html                       ← Paper collection
│   └── about.html
│
├── papers/                               ← Input PDFs (30 papers)
│   ├── 1111.0931.pdf
│   ├── 1601.06839.pdf
│   └── ...
│
└── rh_corpus_database.json              ← Generated database (root level)
```

---

## 🎨 Customization Examples

### Change Node Colors (Citation Network)
```python
role_colors = {
    "H13": "#10b981",       # green
    "H14": "#3b82f6",       # blue
    "H15": "#ef4444",       # red
    "Phase_NB": "#f59e0b",  # amber
    "Spectral": "#8b5cf6",  # purple (add custom)
}
```

### Filter Network by Strength
```python
strong_edges = [c for c in db.connections if c.strength > 0.7]
for conn in strong_edges:
    G.add_edge(conn.source_id, conn.target_id)
```

### Change Timeline Grouping
```python
# Instead of "role_in_project", group by mathematical domain
timeline_df['Domain'] = timeline_df['ID'].map(lambda id: get_domain(id))
```

### Add New Visualization Type
```python
# E.g., "Author Collaboration Network"
author_graph = nx.Graph()
for article in db.articles:
    for author1 in article.authors:
        for author2 in article.authors:
            author_graph.add_edge(author1.name, author2.name)
net = Network()
net.from_nx(author_graph)
net.show('author_network.html')
```

See `VISUALIZATION_WORKFLOW.md` for more examples.

---

## 🔍 Querying the Database

### JSON Query (Python)
```python
import json

with open('rh_corpus_database.json') as f:
    db = json.load(f)

# Find all H15 papers
h15_papers = [a for a in db['articles'] if a['role_in_project'] == 'H15']

# Find papers by author
author_papers = [a for a in db['articles'] if any(aut['name'] == 'Bettin' for aut in a['authors'])]

# Find papers mentioning "Möbius"
mobius_papers = [a for a in db['articles'] if 'möbius' in ' '.join(a.get('tags', [])).lower()]
```

### SQLite Query (SQL)
```sql
-- Find all H15 papers, most recent first
SELECT id, title, year FROM articles 
WHERE role_in_project = 'H15' 
ORDER BY year DESC;

-- Find most-connected papers (citation hubs)
SELECT source_id, COUNT(*) as inbound 
FROM connections 
GROUP BY source_id 
ORDER BY inbound DESC 
LIMIT 10;

-- Find papers with high formalization readiness
SELECT a.title, f.overall_readiness 
FROM articles a 
JOIN formalization f ON a.id = f.article_id 
WHERE f.overall_readiness > 0.7;
```

---

## 🐛 Debugging & Troubleshooting

### Blank Visualization
**Symptom:** Opening `citation_network.html` shows blank page  
**Cause:** Pyvis HTML wasn't generated  
**Fix:** Ensure notebook cell "VIZ 1" runs successfully; check `./visualizations/` folder

### Missing Dependencies
**Symptom:** `ModuleNotFoundError: No module named 'networkx'`  
**Fix:**
```bash
pip install networkx pyvis altair plotly scikit-learn umap-learn marker-pdf
```

### t-SNE Perplexity Error
**Symptom:** "perplexity is too large"  
**Cause:** Too few data points (less than 5 papers with intuitions)  
**Fix:** Ensure sample database has at least 5 intuitions, or adjust perplexity:
```python
perplexity = min(5, len(X) - 1)  # Already in notebook
```

### Network Graph Too Dense
**Symptom:** Citation network is unreadable, all nodes connected  
**Fix:** Filter by edge strength:
```python
threshold = 0.6
strong_connections = [c for c in db.connections if c.strength > threshold]
for conn in strong_connections:
    G.add_edge(conn.source_id, conn.target_id)
```

---

## 📚 Learning Resources

- **Pydantic:** https://docs.pydantic.dev/
- **NetworkX:** https://networkx.org/documentation/stable/
- **Pyvis:** https://pyvis.readthedocs.io/
- **Altair:** https://altair-viz.github.io/user_guide/
- **Plotly:** https://plotly.com/python/
- **t-SNE/UMAP:** https://pair-code.github.io/understanding-umap/

---

## 🚦 Next Steps

1. **Run the notebook:** `jupyter notebook 01_parse_and_visualize.ipynb`
2. **Verify outputs:** Check `visualizations/` folder for 4 HTML/SVG files
3. **Deploy to website:** Copy to `doc/html/visualizations/`
4. **Test in browser:** Open `doc/html/visualizations.html`
5. **Add more papers:** Place PDFs in `papers/`, re-run notebook
6. **Extend schema:** Add fields to Pydantic models as needed
7. **Create custom dashboards:** Build HTML/JS frontends using the JSON database

---

## 💡 Tips & Tricks

- **Use Jupyter dark mode:** Easier on the eyes for long sessions
- **Save intermediate outputs:** Comment out `net.show()` to save without opening browser
- **Version control database:** Commit `rh_corpus_database.json` to track changes
- **Automate with cron:** Use a cron job to regenerate visualizations weekly
- **Monitor graph metrics:** Add `print(f"Nodes: {G.number_of_nodes()}, Edges: {G.number_of_edges()}")` for sanity checks

---

## 📧 Support & Contributing

For questions or to extend this system:
1. Check `VISUALIZATION_WORKFLOW.md` for detailed instructions
2. Review `SCHEMA_MATHLIT_DATABASE.md` to understand the data model
3. Examine `01_parse_and_visualize.ipynb` source code
4. Contact: scai@sorbonne-universite.fr

---

**Created:** 2026-07-15  
**Last Updated:** 2026-07-15  
**Version:** 1.0  
**Status:** Ready for Production
