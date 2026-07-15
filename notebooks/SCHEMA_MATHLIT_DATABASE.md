# Mathematical Literature Database Schema
## Structured JSON/SQLite for RH Corpus Parsing

**Objective:** Create a machine-readable database of mathematical papers with Lean formalization potential, concept mappings, and proof structure.

**Tech Stack:**
- **PDF → Markdown:** Marker or GROBID (preserves LaTeX equations)
- **Structured Parsing:** Instructor + Claude API (enforce Pydantic schema)
- **Storage:** SQLite (relational) or JSON (flat, human-readable)
- **Visualization:** NetworkX + Pyvis (interactive concept graphs)

---

## 1. ARTICLE Reference Schema

```python
from pydantic import BaseModel, Field
from typing import List, Optional
from datetime import date

class Author(BaseModel):
    name: str
    affiliation: Optional[str] = None
    role: str = Field(
        default="author",
        description="author | reviewer | commenter"
    )

class ArticleReference(BaseModel):
    """Core bibliographic data"""
    id: str = Field(description="unique identifier: arxiv:XXXX.XXXXX or doi:...")
    title: str
    authors: List[Author]
    year: int
    journal: Optional[str] = None
    arxiv_id: Optional[str] = None
    doi: Optional[str] = None
    published_date: Optional[date] = None
    pages: Optional[str] = None
    url: Optional[str] = None
    local_pdf_path: str = Field(description="path in /papers/")
    
    # Metadata for project relevance
    role_in_project: str = Field(
        description="H13 | H14 | H15 | Phase_NB | Spectral | Analytic | Probabilistic | Functional | General"
    )
    relevance_score: float = Field(
        ge=0, le=1, description="0.0-1.0, human-assigned or LLM-estimated"
    )
    tags: List[str] = Field(
        description="keyword tags: zeta-function, möbius, period-functions, mellin, etc."
    )
```

---

## 2. KEY MATH INSIGHTS Schema

```python
class Theorem(BaseModel):
    """A standalone theorem or proposition"""
    label: str = Field(description="e.g., 'Theorem 3.1', 'Prop. 5'")
    statement: str = Field(description="Informal statement in LaTeX-compatible form")
    formal_statement: Optional[str] = Field(
        None, description="Formal statement, if extracted"
    )
    proof_sketch: Optional[str] = Field(None, description="1-2 sentence proof idea")
    assumptions: List[str] = Field(default=[], description="required lemmas, definitions, or RH assumptions")
    conclusion: str = Field(description="what the theorem guarantees")
    confidence: float = Field(
        default=0.8, ge=0, le=1, description="How confident is this extraction? LLM confidence or human review."
    )

class Technique(BaseModel):
    """A proof technique or method"""
    name: str = Field(description="e.g., mollifiers, sieve methods, trace formulas, Perron inversion")
    description: str
    used_in: List[str] = Field(description="list of theorem labels that use this technique")
    prerequisites: List[str] = Field(
        description="other techniques or background needed to understand this one"
    )

class MathematicalObject(BaseModel):
    """A key mathematical structure"""
    name: str = Field(description="e.g., Riemann zeta, Möbius function, L-function")
    category: str = Field(description="function | kernel | distribution | space | operator | etc.")
    definition: str = Field(description="brief definition or reference")
    key_properties: List[str] = Field(description="important properties or bounds")
    related_objects: List[str] = Field(description="other objects it interacts with")

class KeyInsights(BaseModel):
    """All mathematical content from a paper"""
    article_id: str
    main_theorem: Optional[Theorem] = None
    key_theorems: List[Theorem] = Field(default=[])
    key_techniques: List[Technique] = Field(default=[])
    mathematical_objects: List[MathematicalObject] = Field(default=[])
    main_contribution: str = Field(
        description="What's genuinely new in this paper? (vs. background)"
    )
    open_problems: List[str] = Field(
        default=[], description="Explicitly stated open questions"
    )
```

---

## 3. INTUITIONS Schema

```python
class Intuition(BaseModel):
    """A heuristic argument, analogy, or non-rigorous justification"""
    type: str = Field(
        description="heuristic | analogy | physical-intuition | toy-model | geometric-picture"
    )
    description: str = Field(description="The intuition in plain language")
    supports_theorem: Optional[str] = Field(None, description="label of theorem this motivates")
    mathematical_basis: Optional[str] = Field(
        None, description="what rigorous result (if any) backs this intuition"
    )
    limitations: Optional[str] = Field(
        None, description="where does the intuition break down?"
    )
    confidence: float = Field(ge=0, le=1, default=0.7)

class MathematicalIntuitions(BaseModel):
    """All intuitions from a paper"""
    article_id: str
    author_intuitions: List[Intuition] = Field(
        description="Heuristics and analogies the authors explicitly give"
    )
    extracted_intuitions: List[Intuition] = Field(
        description="Heuristics we infer from the proof structure"
    )
    connection_to_other_routes: Optional[str] = Field(
        None, description="Does this paper connect to Spectral, Analytic, Probabilistic routes?"
    )
```

---

## 4. LEAN FORMALIZATION POTENTIAL Schema

```python
class LeanDependency(BaseModel):
    """A Mathlib dependency or gap"""
    concept: str = Field(description="e.g., 'perfectoid spaces', 'Mellin transform'")
    status: str = Field(
        description="available-in-mathlib | available-but-scattered | custom-dependency | no-formalization-yet"
    )
    mathlib_module: Optional[str] = Field(
        None, description="path like 'Analysis.SpecialFunctions.Zeta' if available"
    )
    gap_description: Optional[str] = Field(
        None, description="what's missing if status != available"
    )
    estimated_effort: Optional[str] = Field(
        None, description="easy | medium | hard | research-level (for custom work)"
    )

class FormalizationPotential(BaseModel):
    """How much of this paper can be formalized in Lean"""
    article_id: str
    
    # Overall readiness
    overall_readiness: float = Field(
        ge=0, le=1, 
        description="0.0 = completely untouched in Lean; 1.0 = fully formalized"
    )
    
    # Which lemmas/theorems are formalizeable
    formalizable_theorems: List[str] = Field(
        description="labels of theorems that are good Lean targets"
    )
    formalizable_techniques: List[str] = Field(
        description="proof techniques we can encode in Lean"
    )
    
    # Dependency gaps
    mathlib_dependencies: List[LeanDependency] = Field(
        default=[], 
        description="What does this paper need from Mathlib?"
    )
    custom_definitions_needed: List[str] = Field(
        default=[],
        description="Custom Lean definitions we'd need to write"
    )
    
    # Effort estimate
    estimated_weeks: Optional[float] = Field(
        None, description="rough person-weeks to formalize the main results"
    )
    
    # Proof structure
    proof_dag: Optional[str] = Field(
        None, 
        description="simplified DAG of main lemma dependencies (as JSON or text)"
    )
    
    notes: Optional[str] = Field(
        None, description="e.g., 'relies on RH explicitly', 'circular reasoning here'"
    )
```

---

## 5. PAPER CONNECTIONS Schema

```python
class Connection(BaseModel):
    """A directed edge between two papers"""
    source_id: str
    target_id: str
    relationship: str = Field(
        description="extends-method | disproves-conjecture-in | provides-function-field-analogue | uses-result-from | inspired-by | alternative-proof-of | recent-breakthrough-in | survey-of"
    )
    description: str = Field(description="How are they connected?")
    strength: float = Field(
        ge=0, le=1, default=0.5, description="how important is this connection?"
    )

class PaperNetwork(BaseModel):
    """Citation and concept graph"""
    connections: List[Connection]
    # Computed fields (generated from analysis):
    clusters: Optional[List[List[str]]] = Field(
        None, description="groups of papers by concept (Spectral, Analytic, etc.)"
    )
    central_papers: Optional[List[str]] = Field(
        None, description="most-connected papers by betweenness centrality"
    )
```

---

## 6. COMPLETE DATABASE SCHEMA

```python
class MathematicalLiteratureDatabase(BaseModel):
    """Complete RH corpus database"""
    version: str = "1.0"
    generated_date: date
    
    # Core collections
    articles: List[ArticleReference]
    insights: List[KeyInsights]
    intuitions: List[MathematicalIntuitions]
    formalization: List[FormalizationPotential]
    network: PaperNetwork
    
    # Metadata
    statistics: dict = Field(
        default={},
        description="e.g., {'total_papers': 30, 'h14_relevant': 12, 'fully_formalizable': 3}"
    )
```

---

## 7. STORAGE OPTIONS

### Option A: JSON (Human-Readable)
```json
{
  "version": "1.0",
  "generated_date": "2026-07-15",
  "articles": [
    {
      "id": "arxiv:1111.0931",
      "title": "Approximations to the Riemann Hypothesis",
      "authors": [...],
      ...
    }
  ],
  "insights": [...],
  "intuitions": [...],
  "formalization": [...],
  "network": {...}
}
```

**Pros:** Human-readable, version-control friendly, easy to parse  
**Cons:** Slow for large databases, not relational

### Option B: SQLite (Relational)
```sql
CREATE TABLE articles (
  id TEXT PRIMARY KEY,
  title TEXT NOT NULL,
  authors JSON,
  year INT,
  role_in_project TEXT,
  ...
);

CREATE TABLE theorems (
  id TEXT PRIMARY KEY,
  article_id TEXT FOREIGN KEY,
  label TEXT,
  statement TEXT,
  ...
);

CREATE TABLE connections (
  source_id TEXT,
  target_id TEXT,
  relationship TEXT,
  ...
);
```

**Pros:** Queryable, efficient, supports relationships  
**Cons:** Less human-readable, requires schema migration

---

## 8. RECOMMENDED APPROACH

**Start with:** JSON + Pydantic (human-readable, version-control friendly)  
**Upgrade to:** SQLite if >100 papers or need complex queries

**Workflow:**
1. Define Pydantic schema (done above)
2. Build LLM parser: PDF → JSON (using Instructor)
3. Validate against schema
4. Export to SQLite for complex analysis
5. Visualize with NetworkX + Pyvis

---

## 9. EXAMPLE: SINGLE PARSED PAPER

```json
{
  "article_id": "arxiv:1111.0931",
  "title": "Approximations to the Riemann Hypothesis",
  "authors": [{"name": "Bettin", "role": "author"}, {"name": "Conrey", "role": "author"}],
  "year": 2013,
  "role_in_project": "H15",
  "relevance_score": 0.95,
  "tags": ["möbius", "period-functions", "cotangent-sums", "vasyunin"],
  
  "main_insights": {
    "main_theorem": {
      "label": "Theorem 1.1",
      "statement": "Period functional equation for cotangent sums",
      "proof_sketch": "Fourier analysis on GL(2)",
      "assumptions": ["Vasyunin identity"]
    },
    "key_techniques": [
      {"name": "period-functions", "description": "..."}
    ]
  },
  
  "intuitions": {
    "author_intuitions": [
      {
        "type": "analogy",
        "description": "Cotangent sums behave like quantum modular forms",
        "confidence": 0.6
      }
    ]
  },
  
  "formalization": {
    "overall_readiness": 0.6,
    "formalizable_theorems": ["Theorem 1.1", "Prop 2.3"],
    "mathlib_dependencies": [
      {
        "concept": "period-functions",
        "status": "custom-dependency",
        "estimated_effort": "medium"
      }
    ],
    "estimated_weeks": 3.5
  },
  
  "connections": [
    {
      "target_id": "arxiv:1601.06839",
      "relationship": "uses-result-from",
      "description": "Auli-Bayad-Beck provide reciprocity machinery that Bettin-Conrey apply"
    }
  ]
}
```

---

## Next Step

Ready to:
1. **Build the parser:** Jupyter notebook using Instructor + Claude API to fill this schema
2. **Test on sample papers:** Start with 3-5 papers from your corpus
3. **Export database:** JSON first, then migrate to SQLite
4. **Visualize:** NetworkX graph of paper connections + Lean readiness dashboard

Which would you prefer: **start with the parser code**, or **refine the schema further first**?
