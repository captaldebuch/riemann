# Artifact Database Roadmap: RH Formalization as Queryable Knowledge

## Vision

Unify papers, intuitions, lemmas, theorems, proofs, and research decisions into a **single queryable knowledge graph** where:
- Every paper is an artifact with parsed concepts and proofs that formalize it
- Every Lean theorem links backward to the papers/intuitions that motivated it
- Every proof step has an audit trail: paper → informal claim → formal statement → Lean proof
- Strategic decisions are captured as first-class artifacts (roadmaps, research gates, diagnostics)
- The entire discovery process is navigable, reproducible, and verifiable

---

## Current State Assessment

### Existing Artifacts (Unconnected)

| Layer | Format | Count | Current Location |
|-------|--------|-------|------------------|
| **Papers** | PDF + JSON metadata | 78 papers | `papers/`, `website/html/knowledge_graphs.json` |
| **Intuitions** | HTML + narrative | 26 mathematicians, 4 routes | `website/html/js/app.js` |
| **Lean Proofs** | `.lean` files + modules | 8,671 jobs verified | `.worktrees/h15-*`, `proofs/` |
| **Theorems** | Lean source + metadata | 500+ proved theorems | Embedded in `.lean` files |
| **Research Decisions** | Markdown + memory | Roadmaps, phase docs | `memory/`, commit messages |
| **Experiments** | Markdown reports | Phase diagnostics | `.worktrees/*/experiments/` |
| **Build Status** | CLI output | Per-commit | `lake build` logs |

### Current Connections (Partial)

- ✅ Papers → concepts (knowledge_graphs.json)
- ✅ Papers → website sections (hard-coded HTML)
- ❌ Papers → Lean theorems (no formal link)
- ❌ Intuitions → theorems (implicit only)
- ❌ Theorems → source papers (backwards link missing)
- ❌ Proofs → conceptual motivation (commit messages only)
- ❌ Research gates → formal statements (implicit)

---

## Proposed Data Model: Artifact Layer

### Three Artifact Classes

#### 1. **Source Artifacts** (Primary references)
- **Papers**: arXiv ID, title, authors, year, concepts, PDF link
- **Mathematicians**: name, period, bio, contributions, key papers
- **Concepts**: name, definition, related papers, first-appearance-year

#### 2. **Formalization Artifacts** (Lean code)
- **Theorems**: name, statement, proof file, line number, commit hash, build status
- **Lemmas**: name, statement, dependencies, proof file
- **Definitions**: type definition, module, docstring, usage count
- **Modules**: purpose, dependencies, job count, axiom audit
- **Proofs**: structure (tactics used), complexity metric, related papers

#### 3. **Research Artifacts** (Discovery process)
- **Research Gates**: name, requirement, blocking issues, estimation
- **Roadmaps**: phases, dependencies, status per phase, decision rationale
- **Diagnostics**: diagnostic ID, data, findings, implications
- **Experiments**: scope, methodology, results, conclusions
- **Decisions**: decision ID, context, options considered, rationale, outcome

---

## Proposed Schema (JSON-LD / RDF)

```json
{
  "@context": "https://rh-formalization.example/schema",
  "@id": "theorem:EhmS1OneSidedCoupledCancellationEstimate",
  "@type": "FormalTheorem",
  
  "name": "EhmS1OneSidedCoupledCancellationEstimate",
  "statement": "|U_N + (G(1,1)−K)D_N + R_N| ≤ C/(log N)^α",
  "formalStatement": "∃ C α > 0, ∀ N, ...",
  
  "source": {
    "file": "BCFLogTaperEhmCompensator.lean",
    "line": 473,
    "commit": "805e208",
    "module": "RiemannHypothesis.Criteria.NymanBeurling"
  },
  
  "motivation": [
    "paper:Ehm:2405.06349",
    "paper:Bettin:1111.0931",
    "concept:CoupledCancellation"
  ],
  
  "dependencies": [
    "lemma:EhmS1PointwiseKernelPackage",
    "lemma:OffDiagonalSymmetrization",
    "lemma:ReciprocalIdentity"
  ],
  
  "verificationStatus": {
    "buildStatus": "passed",
    "jobCount": 8660,
    "newAxioms": 0,
    "sorries": 0,
    "timestamp": "2026-07-22T10:45:00Z"
  },
  
  "researchGate": "gate:SignedBoundaryEstimate",
  "openProblem": true,
  "difficulty": "RH-strength"
}
```

---

## Implementation Roadmap (4 Phases)

### Phase 1: Schema & Artifact Ingestion (Weeks 1–2)

**Goal:** Extract and structure all artifacts in a canonical JSON-LD format.

**Tasks:**
1. Define `artifact.schema.json` (extends JSON-LD)
   - Core properties: @id, @type, name, statement, source, motivation, verification
   - Relationships: `dependsOn`, `motivatedBy`, `formalizes`, `instantiatesGate`

2. Build ingestion pipeline (Python):
   - Parse `.lean` files → extract theorems with metadata (name, statement, line, commit)
   - Extract paper metadata → standard artifact format
   - Parse memory files → research gates and roadmaps as artifacts
   - Parse commit messages → decision artifacts with rationale

3. Seed initial artifact registry (`artifacts/registry.jsonld`):
   - 500+ Lean theorems with source location + commit
   - 78 papers with concept tags
   - 26 mathematician profiles
   - 10 research gates with status

4. Link papers to theorems (semi-manual initial pass):
   - Use commit messages + file names to infer "paper → theorem" relationships
   - Annotate: `Ehm:2405.06349` formalized as theorems X, Y, Z (commits A, B, C)

**Deliverable:** `artifacts/` directory with 600+ JSON-LD artifacts, bidirectional metadata.

---

### Phase 2: Graph Database & Query Layer (Weeks 3–4)

**Goal:** Make artifacts queryable; surface hidden connections.

**Tasks:**
1. Load artifact registry into lightweight graph DB:
   - Option A: **Neo4j** (property graphs, Cypher query language)
   - Option B: **RDF store** (Apache Jena, SPARQL)
   - Option C: **Custom SQLite** (JSON columns + foreign keys) — minimal dependency

   Recommend **Option C** initially (no external service; queryable via CLI).

2. Build query CLI tool (`scripts/query-artifacts.py`):
   ```bash
   # "Which papers formalize into which theorems?"
   ./scripts/query-artifacts.py --from papers --to theorems --paper "Ehm:2405.06349"
   
   # "What research gate blocks this theorem?"
   ./scripts/query-artifacts.py --gate-blocks "EhmS1OneSidedCoupledCancellationEstimate"
   
   # "Show the proof DAG for this theorem"
   ./scripts/query-artifacts.py --proof-dag "EhmS1OneSidedCoupledCancellationEstimate" --depth 3
   
   # "List all open problems with RH-strength difficulty"
   ./scripts/query-artifacts.py --open-problems --difficulty "RH-strength"
   ```

3. Build indexer (`scripts/build-artifact-index.py`):
   - Watches `.lean` files + memory + commits
   - On change: re-extract, re-link, update DB
   - Runs post-commit hook (optional)

4. Audit & validation:
   - Check for orphaned artifacts (no incoming links)
   - Check for circular dependencies
   - Verify every theorem has a commit/line reference
   - List incomplete metadata (missing motivation, open problems)

**Deliverable:** Queryable artifact database; CLI tool for discovery; indexer script.

---

### Phase 3: Enhanced Website Integration (Weeks 5–6)

**Goal:** Surface artifact relationships in the website; make discovery interactive.

**Tasks:**
1. Extend website with **Artifact Explorer** page:
   - Search by artifact ID, type, property
   - Click theorem → see proof DAG, source papers, research gate, commit history
   - Click paper → see all theorems that formalize it
   - Click concept → see genealogy (first appearance → related papers → formalizing theorems)

2. Add **Proof Narrative** viewer:
   - Theorem statement
   - Motivation (papers + intuitions)
   - Proof outline (tactic structure)
   - Dependencies (tree view)
   - Commit link + full source

3. Add **Paper-to-Theorem** mapping visualization:
   - Force-directed graph: papers as nodes, edges labeled with theorem names
   - Animated view: highlight the path from paper claim → formal statement → Lean proof

4. Add **Research Gate Dashboard**:
   - Table of all open problems
   - For each: blocking theorems, attempted strategies, current best approach, difficulty estimate
   - Links to relevant diagnostics + experiments

5. Extend search index:
   - Full-text search: papers + theorems + concepts + intuitions
   - Faceted search: by difficulty, by route, by status

**Deliverable:** Interactive artifact explorer; proof narratives; paper-to-theorem visualization; research gate dashboard.

---

### Phase 4: Formalization Tooling & Audit Trail (Weeks 7–8)

**Goal:** Make the formalization process itself an artifact; enable reproducible proof discovery.

**Tasks:**
1. **Proof Template** generator:
   - Ingests: (paper claim, informal proof sketch, Lean goal state)
   - Outputs: Lean skeleton with TODO markers at key steps
   - Records template ID for later reference

2. **Audit Trail** recorder:
   - On every `lake build`: record
     - Commit hash
     - Modules built
     - New theorems (name, statement, source location)
     - Any new sorries/axioms
     - Build time
   - Store as `build-artifacts/COMMIT_HASH.json`
   - Allows reconstruction of formalization history

3. **Theorem Evolution** tracker:
   - Which theorems changed between commits
   - How statements changed (stmt diff)
   - When proofs transitioned from `sorry` → complete
   - Visualization: timeline of theorem maturation

4. **Diagnostic Embedding**:
   - Attach diagnostic reports to relevant theorems/gates
   - E.g., `BCFLogTaperEhmCompensator.lean:136` → diagnostic `phase15_ehm_ratio_sector_diagnostics.md:80`
   - Query: "Show me data supporting this theorem"

5. **Decision Journal**:
   - Each research decision logged with:
     - Context (what was the problem)
     - Options considered (with pro/con)
     - Choice made (with rationale)
     - Outcome (what we learned)
   - Example: "Why do we use cofinal rather than uniform bounds?"

**Deliverable:** Proof templates; audit trail database; theorem evolution timeline; decision journal.

---

## Architecture Diagram

```
┌─────────────────────────────────────────────────────────────┐
│                    ARTIFACT DATABASE                         │
│                                                               │
│  ┌──────────────────────────────────────────────────────┐   │
│  │  Canonical Artifact Registry (JSON-LD)              │   │
│  │  - 500+ Lean theorems                               │   │
│  │  - 78 papers + concepts                             │   │
│  │  - 26 mathematicians                                │   │
│  │  - 10+ research gates + roadmaps                    │   │
│  │  - 20+ experiments + diagnostics                    │   │
│  └──────────────────────────────────────────────────────┘   │
│                           ↓                                   │
│  ┌──────────────────────────────────────────────────────┐   │
│  │  Graph Layer (SQLite + Query CLI)                   │   │
│  │  - Relationships: motivatedBy, formalizes,          │   │
│  │    dependsOn, blockedBy, instantiates               │   │
│  │  - Indexer (watches .lean + commits)                │   │
│  └──────────────────────────────────────────────────────┘   │
│         ↙                    ↓                    ↖            │
│    ┌────────────┐      ┌─────────────┐      ┌────────────┐  │
│    │   CLI      │      │  Website    │      │  Audit     │  │
│    │  Queries   │      │  Explorer   │      │  Trail DB  │  │
│    └────────────┘      └─────────────┘      └────────────┘  │
└─────────────────────────────────────────────────────────────┘
```

---

## Benefits

### For Discovery
- **"What papers does this proof build on?"** — follow backward links
- **"What theorems does this paper contribute?"** — forward discovery
- **"What open problems remain?"** — query by difficulty/gate status
- **"Show me the dependency graph for RH"** — entire proof DAG

### For Verification
- **Proof reproducibility**: every theorem → commit → can rebuild
- **Axiom audit**: track where classical axioms enter; when they're eliminated
- **Sorry tracking**: find all incomplete proofs; see maturation timeline

### For Collaboration
- **"What should I work on next?"** — query open problems by estimated difficulty
- **"What's the intuition here?"** — link theorem to original paper + mathematicians
- **"Why did we choose this approach?"** — decision journal + diagnostics

### For Communication
- **Paper → Theorem mapping**: publish as supplementary material
- **Proof narratives**: each theorem tells its story (motivation → proof → impact)
- **Interactive website**: explore RH as a connected knowledge space, not isolated documents

---

## Implementation Strategy

### Quick Start (2–3 days)
1. Manual curation: pick 20 key theorems (H13, H14, Phase NB, H15 gates)
2. Write schemas (artifact.schema.json, relationships.schema.json)
3. Create CSV ingestion → JSON-LD converter
4. Seed artifacts directory; link on website

### Medium Term (2–3 weeks)
1. Automated `.lean` parsing → artifact extraction
2. SQLite graph + query CLI
3. Integration hook (post-commit artifact indexing)
4. Enhanced website explorer

### Long Term (ongoing)
1. Theorem evolution tracking
2. Decision journal formalization
3. Proof template generation
4. Community artifact contribution system

---

## Files to Create

```
artifacts/
├── schema/
│   ├── artifact.schema.json
│   ├── relationships.schema.json
│   └── metadata.schema.json
├── registry.jsonld
├── papers/
│   ├── Ehm:2405.06349.json
│   ├── Bettin:1111.0931.json
│   └── ...
├── theorems/
│   ├── EhmS1OneSidedCoupledCancellationEstimate.json
│   ├── OffDiagonalSymmetrization.json
│   └── ...
├── gates/
│   ├── SignedBoundaryEstimate.json
│   └── ...
└── decisions/
    ├── why-cofinal-not-uniform.json
    └── ...

scripts/
├── ingest-artifacts.py          # Parse .lean → extract theorems
├── ingest-papers.py              # Parse papers → artifact format
├── ingest-memory.py              # Parse memory files → gates/roadmaps
├── build-artifact-index.py       # Load registry → SQLite
├── query-artifacts.py            # CLI for graph queries
└── theorem-evolution-tracker.py  # Track proof maturation

website/html/
├── artifact-explorer.html        # New page: browse artifacts
├── js/artifact-queries.js        # Query integration
└── css/artifact-explorer.css     # Styling
```

---

## Success Metrics

1. **Coverage**: 90%+ of theorems have linked papers + motivation
2. **Queryability**: Can answer "Why do we use this approach?" in < 2 seconds
3. **Reproducibility**: Every theorem can be traced back to paper + commit
4. **Discoverability**: Website artifact explorer gets >50% click-through from main navigation
5. **Decision audit**: All major research decisions documented with rationale

---

## Next Steps

1. **This week**: Approve schema; start manual curation of 20 key theorems
2. **Next week**: Build ingestion pipeline; seed artifacts directory
3. **Following**: Query CLI; website integration
4. **Month 2**: Audit trail + decision journal
5. **Month 3+**: Community contribution system; published supplementary materials

