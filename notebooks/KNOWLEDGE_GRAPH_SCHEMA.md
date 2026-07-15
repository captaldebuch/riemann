# Mathematical Knowledge Graph Schema
## Structured Data Model for Papers as Knowledge Objects

**Objective:** Transform mathematical papers into richly interconnected knowledge graphs with 10 dimensions of mathematical structure.

---

## Core Entities

### 1. Mathematical Objects

```python
class MathematicalObject(BaseModel):
    id: str  # "Theorem_1", "Def_Adele_Ring", "Lemma_7"
    type: str  # "theorem", "definition", "lemma", "conjecture", "corollary", "assumption"
    name: str  # "Explicit Formula for L-Functions"
    statement: str  # Formal or semi-formal statement
    section: Optional[str]  # Where in paper it appears
    assumptions: List[str]  # Assumptions it requires (ids)
    conclusion: str  # What it claims/defines
    context: Optional[str]  # Heuristic or motivation

class Proof(BaseModel):
    id: str  # "Proof_Theorem_1"
    theorem_id: str  # Which theorem it proves
    steps: List[ProofStep]
    uses_lemmas: List[str]  # Lemma ids
    uses_tools: List[str]  # Tool ids (e.g., "Fourier_Transform")
    key_insight: Optional[str]  # What makes it work
    length_estimate: Optional[str]  # "3 pages", "1 line"

class ProofStep(BaseModel):
    index: int
    description: str
    justification: List[str]  # Lemmas, tools, previous steps
    equation_refs: List[str]  # References to equations

class Equation(BaseModel):
    id: str  # "Eq_Trace_Formula"
    latex: str  # The equation in LaTeX
    meaning: str  # What the equation represents
    context: str  # Where it appears
    related_theorems: List[str]  # Theorems using this
    related_definitions: List[str]  # Definitions using this
```

---

## Knowledge Graph Edges

### 2. Dependency Graph

```python
class Dependency(BaseModel):
    source_id: str  # Theorem or proof that depends
    target_id: str  # Theorem or lemma it depends on
    type: str  # "requires", "uses", "generalizes", "specializes"
    strength: float  # 0.0-1.0 (critical vs. optional)
    explanation: Optional[str]  # Why the dependency exists

class DependencyGraph(BaseModel):
    paper_id: str
    nodes: List[str]  # All theorem/lemma/definition ids
    edges: List[Dependency]
    # Computed:
    critical_path: List[str]  # Theorems needed first
    dependencies_count: Dict[str, int]  # How many things depend on each
```

### 3. Conceptual Analogy Dictionary

```python
class Analogy(BaseModel):
    id: str  # "Dict_AG_NT"
    source_domain: str  # "Algebraic Geometry"
    target_domain: str  # "Number Theory"
    mappings: List[AnalogyMapping]
    strength: float  # How close the analogy is

class AnalogyMapping(BaseModel):
    source_concept: str  # AG concept
    target_concept: str  # NT concept
    explanation: str  # How they correspond
    example_theorem: Optional[str]  # Where this is used
```

### 4. Proof Tools & Techniques

```python
class ProofTool(BaseModel):
    id: str  # "Fourier_Transform", "Parseval_Formula"
    name: str
    description: str
    domain: str  # "Harmonic Analysis", "Complex Analysis"
    used_in_theorems: List[str]  # Which theorems use this
    related_tools: List[str]  # Complementary tools
    references: List[str]  # Who proved/introduced this
```

---

## Knowledge Dimensions

### 5. Timeline of Influences

```python
class Influence(BaseModel):
    influenced_by_id: str  # Ref or theorem id
    influenced_theorem_id: str  # What it influenced
    type: str  # "inspired", "extends", "generalizes", "analogous"
    explanation: str
    historical_context: Optional[str]

class InfluenceTimeline(BaseModel):
    paper_id: str
    influences: List[Influence]
    # Visualization: Timeline showing flow of ideas
```

### 6. Assumptions & Their Resolution

```python
class Assumption(BaseModel):
    id: str  # "Assumption_delta", "Assumption_S"
    statement: str
    introduced_in: str  # Section or theorem
    used_in: List[str]  # Theorems/lemmas using it
    status: str  # "active", "eliminated", "relaxed", "conditional"
    elimination_section: Optional[str]  # Where it's removed
    alternative_if_removed: Optional[str]  # What changes without it

class AssumptionTracker(BaseModel):
    paper_id: str
    assumptions: List[Assumption]
    # Summary: Which assumptions are critical to the main result?
```

### 7. Notation Glossary

```python
class Symbol(BaseModel):
    latex: str  # The symbol in LaTeX (e.g., "\\Delta")
    name: str  # Human-readable name
    meaning: str  # Mathematical meaning
    first_appearance: str  # Section
    uses: List[str]  # Theorems/equations where used
    related_symbols: List[str]  # Similar or complementary symbols

class NotationGlossary(BaseModel):
    paper_id: str
    symbols: List[Symbol]
    # Searchable: hover/search functionality
```

### 8. Open Problems & Conjectures

```python
class OpenProblem(BaseModel):
    id: str  # "Conjecture_RH", "Problem_Trace_Formula_Global"
    statement: str
    introduced_by: Optional[str]  # Who posed it
    related_to_theorem: Optional[str]  # Which theorem in this paper
    importance: str  # "foundational", "important", "interesting"
    potential_impact: str  # What would solving it enable?
    status: str  # "open", "solved", "partially_solved"

class OpenProblemsDB(BaseModel):
    paper_id: str
    problems: List[OpenProblem]
    connections: Dict[str, List[str]]  # Which theorems discuss each problem
```

---

## Historical & Contextual Data

### 9. References & Citations

```python
class Reference(BaseModel):
    id: str  # "Ref_Weil_1952"
    author: str
    year: int
    title: str
    journal_or_book: str
    cited_in: List[str]  # Which theorems/proofs cite this
    type: str  # "foundational", "technique", "related_result", "historical"
    influence_level: str  # "critical", "important", "supporting"

class HistoricalMap(BaseModel):
    paper_id: str
    references: List[Reference]
    influences: List[Influence]  # Who influenced whom
    # Visualization: network showing intellectual lineage
```

### 10. Proof Trace & Tool Usage

```python
class ProofTrace(BaseModel):
    paper_id: str
    proofs: List[Proof]
    # Analytics:
    most_complex_proof: str  # Theorem id
    tool_frequency: Dict[str, int]  # How often each tool is used
    common_proof_patterns: List[str]  # Repeated structures
    dependency_depth: Dict[str, int]  # How deep the dependencies
```

---

## Aggregate Knowledge Graph

```python
class MathematicalPaperKnowledgeGraph(BaseModel):
    """Complete structured representation of a paper as a knowledge graph"""
    
    paper_id: str
    
    # Core entities
    objects: Dict[str, MathematicalObject]  # id → object
    proofs: Dict[str, Proof]  # id → proof
    equations: Dict[str, Equation]  # id → equation
    tools: Dict[str, ProofTool]  # id → tool
    symbols: List[Symbol]  # All notation
    
    # Graphs & relationships
    dependency_graph: DependencyGraph
    influence_timeline: InfluenceTimeline
    historical_map: HistoricalMap
    assumption_tracker: AssumptionTracker
    
    # Analogies & open problems
    analogies: List[Analogy]
    open_problems: OpenProblemsDB
    
    # Aggregate stats
    statistics: Dict[str, Any]  # Total theorems, lemmas, etc.
    
    # Visualization metadata
    layout_hint: str  # "force-directed", "hierarchical", "circular"
    interactive_elements: List[str]  # What can be clicked/hovered
```

---

## Data Format: JSON-LD

```json
{
  "@context": {
    "@vocab": "https://example.org/mathematics#",
    "rdf": "http://www.w3.org/1999/02/22-rdf-syntax-ns#",
    "theorem": { "@type": "Theorem" },
    "dependsOn": { "@type": "@id" },
    "usedIn": { "@type": "@id" }
  },
  
  "id": "paper:riemann-hypothesis-corpus",
  "title": "Mathematical Knowledge Graph: [Paper]",
  
  "theorems": [
    {
      "id": "theorem:explicit-formula",
      "name": "Explicit Formula for L-Functions",
      "statement": "...",
      "dependsOn": ["theorem:fourier-inversion", "definition:dirichlet-characters"],
      "usedIn": ["theorem:main-result", "proof:symmetric-sum"]
    }
  ],
  
  "proofs": [
    {
      "id": "proof:explicit-formula",
      "proves": "theorem:explicit-formula",
      "steps": [...],
      "uses": ["lemma:contour-shift", "tool:residue-calculus"]
    }
  ],
  
  "dependencies": [
    {
      "source": "theorem:main-result",
      "target": "theorem:explicit-formula",
      "type": "requires",
      "strength": 0.95
    }
  ]
}
```

---

## Visualization Strategy

### Knowledge Graph (Interactive Network)
- Nodes: Theorems (circles), lemmas (squares), tools (diamonds)
- Edges: Dependencies (solid), uses (dashed), influences (dotted)
- Color: By domain or by critical-path status
- Size: By importance or usage frequency

### Proof Explorer
- Hierarchical: Main theorem → lemmas → base cases
- Expandable: Click to see proof steps
- Links: Jump to definitions, tools, previous lemmas

### Timeline of Influences
- X-axis: Publication year
- Y-axis: Research area
- Edges: Citation and influence relationships
- Interactive: Click reference to see its impact

### Assumption Tracker
- Table: All assumptions with status
- Visual flow: Show where assumptions are used
- Interactive: Toggle assumption to see downstream impact

### Notation Glossary
- Searchable: Find symbol by name or pattern
- Hover: See definition and usage context
- Links: Jump to equations/theorems using the symbol

---

## Technical Stack

**Data Storage:**
- Graph Database: Neo4j (for knowledge graph queries)
- JSON Storage: PostgreSQL JSONB (for full documents)
- RDF Triple Store: Optional (for semantic interoperability)

**Extraction:**
- LaTeX Parser: pandoc, pdfminer, or custom regex
- NER: spaCy + custom mathematical entity recognition
- Dependency Analysis: Custom AST parser for Lean/Isabelle proofs

**Visualization:**
- Knowledge Graph: D3.js, Cytoscape.js, or Gephi
- Timeline: Timeline.js, Apache ECharts
- Interactive Paper: PDF.js overlay + custom annotations

**API:**
- GraphQL: Query knowledge graph
- REST: Standard CRUD operations
- WebSockets: Real-time collaboration annotations

---

## Workflow

1. **Parse Paper** → Extract text, equations, structure
2. **Identify Entities** → Theorems, definitions, proofs, tools
3. **Build Dependency Graph** → What depends on what?
4. **Extract Analogies** → Mappings between domains
5. **Timeline Influences** → Who cited whom?
6. **Structured Export** → JSON-LD + Neo4j
7. **Visualize** → Interactive knowledge graph
8. **Collaborate** → Annotate, correct, extend

---

## Example: Trace Formula Paper

**Knowledge Graph for "Selberg Trace Formula":**

```
Theorem_Trace_Formula (depends on)
  ├─ Lemma_Spectral_Expansion (depends on)
  │  ├─ Def_Eigenvalues
  │  └─ Tool_Fourier_Analysis
  ├─ Lemma_Poisson_Summation (depends on)
  │  └─ Theorem_Fourier_Inversion
  └─ Assumption_Compact_Support

Influence_Timeline:
  Ref_Weyl_1911 → Ref_Selberg_1956 → Ref_Connes_1999

Open_Problems:
  - Generalize to non-compact locally symmetric spaces
  - Extend to higher-rank groups
  - Connection to quantum chaos
```

---

This schema enables:
- ✅ Deep mathematical understanding (every theorem's dependencies visible)
- ✅ Interactive exploration (click to drill down)
- ✅ Historical context (see the intellectual lineage)
- ✅ Proof understanding (trace each step)
- ✅ Discovery (find related theorems, tools, problems)
- ✅ Collaboration (annotate, correct, extend)
