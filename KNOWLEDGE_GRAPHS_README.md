# Knowledge Graph Integration for RH Corpus

## What Is This?

Every paper in the corpus has been analyzed and structured as an **interactive knowledge graph** showing:

- **Key Concepts:** Mathematical themes (Möbius Functions, Zeta Functions, Mellin Transforms, etc.)
- **Mathematical Tools:** Fourier Analysis, Contour Integration, Residue Calculus, etc.
- **Related Papers:** Other papers in the same formalization phase
- **Statistics:** Relevance score, author count, phase classification

## How to Use

### For Browsing Individual Papers

Each paper has its own knowledge graph page:
- **URL Format:** `kg_<paper-id>.html`
- **Example:** `kg_1111.0931.html` for Bettin-Conrey 2013
- **Access via:** Corpus page links (coming soon)

### To Explore All Papers

Visit the **Knowledge Graph Explorer:**
- **URL:** `knowledge-explorer.html`
- **Shows:** All papers organized by phase
- **Includes:** Concept cloud across entire corpus

### Navigation

From any page, click the **🔗 Knowledge Graph** link in the top navigation menu.

## What's in Each Paper's Knowledge Graph?

### 1. **Phase Classification**
- Classical Foundation
- Quantitative Bounds
- Cancellation Structure
- General Theory
- Alternative Routes

### 2. **Key Concepts**
Tagged mathematical themes extracted from paper metadata:
- Möbius Functions
- Vasyunin Cotangent Sums
- Period Functions
- Zeta Functions
- Mellin Transform
- Fourier Analysis
- etc.

### 3. **Mathematical Tools**
Techniques and methods mentioned in the paper:
- Fourier Analysis
- Mellin Transform
- Contour Integration
- Residue Calculus
- Explicit Formulas

### 4. **Related Papers**
Links to other papers in the same phase of the RH formalization project.

### 5. **Statistics**
- Relevance score to RH (0.0–1.0)
- Number of authors
- Publication year
- Phase classification

## File Structure

```
doc/html/
  ├── knowledge-explorer.html       ← Start here: overview of all papers
  ├── kg_2607.09797.html           ← Individual paper 1
  ├── kg_2607.09110.html           ← Individual paper 2
  ├── kg_1111.0931.html            ← Individual paper 3
  ├── kg_math_0306251.html         ← etc. (30 total)
  ├── knowledge_graphs.json         ← Raw data export (JSON)
  └── KNOWLEDGE_GRAPHS_README.md   ← This file
```

## Data Format

The raw data is exported as JSON-LD (semantic web standard):
```json
{
  "paper_id": "1111.0931",
  "title": "Approximations to the Riemann Hypothesis",
  "authors": ["Bettin", "Conrey"],
  "year": 2013,
  "phase": "Quantitative Bounds",
  "key_concepts": ["Period Functions", "Möbius Functions"],
  "tools_used": ["Fourier Analysis", "Mellin Transform"],
  "related_papers": ["2607.09797", "1601.06839"],
  "statistics": {
    "relevance_score": 0.95,
    "authors_count": 2
  }
}
```

## Next Steps

This is **Phase 1** of the knowledge graph system. Future enhancements:

### Phase 2: Full Extraction
- Extract theorem statements and dependencies
- Parse proof structure (steps, justifications)
- Map assumption tracking and resolution
- Identify open problems

### Phase 3: Interactive Visualizations
- Interactive network graphs (D3.js / Cytoscape.js)
- Theorem dependency visualization
- Timeline of mathematical influences
- Concept clustering and embeddings

### Phase 4: Neo4j Database
- Deploy graph database for complex queries
- SPARQL queries across all papers
- Recommendation engine (find related theorems)
- Critical path analysis

## Architecture

```
Papers
  ↓ (Extract metadata + contributions)
30 Knowledge Graphs
  ↓ (Generate HTML pages)
Static Website Pages
  ↓ (Display and navigate)
Users exploring corpus
```

## Performance

- **30 papers** analyzed
- **30 HTML pages** generated (~2KB–5KB each)
- **1 JSON export** with full data (~200KB)
- **Zero external dependencies** (offline-capable)
- **Fast load times** (<1s per page)

## Contact

Questions about the knowledge graphs?
- **Project Lead:** Xavier Fresquet
- **Email:** xavier.fresquet@sorbonne.ae
- **Institution:** SCAI (Sorbonne Centre for Artificial Intelligence)

---

*Generated 2026-07-15 | Knowledge Graph System v1.0*
