#!/usr/bin/env python3
"""
Mathematical Knowledge Graph Parser
Extracts 10 knowledge dimensions from papers into structured graphs
"""

from pydantic import BaseModel, Field
from typing import List, Optional, Dict, Any
from datetime import date
import json

# ============================================================================
# ENTITY MODELS (Knowledge Dimensions 1-10)
# ============================================================================

# 1. Mathematical Objects
class MathematicalObject(BaseModel):
    id: str
    type: str  # "theorem", "definition", "lemma", "conjecture", "corollary", "assumption"
    name: str
    statement: str
    section: Optional[str] = None
    assumptions: List[str] = []
    conclusion: str
    context: Optional[str] = None
    confidence: float = 0.8

# 2. Proof Steps & Structure
class ProofStep(BaseModel):
    index: int
    description: str
    justification: List[str] = []
    equation_refs: List[str] = []

class Proof(BaseModel):
    id: str
    theorem_id: str
    steps: List[ProofStep] = []
    uses_lemmas: List[str] = []
    uses_tools: List[str] = []
    key_insight: Optional[str] = None
    length_estimate: Optional[str] = None

# 3. Equations & Notation
class Equation(BaseModel):
    id: str
    latex: str
    meaning: str
    context: str
    related_theorems: List[str] = []
    related_definitions: List[str] = []

class Symbol(BaseModel):
    latex: str
    name: str
    meaning: str
    first_appearance: Optional[str] = None
    uses: List[str] = []
    related_symbols: List[str] = []

# 4. Dependencies & Relationships
class Dependency(BaseModel):
    source_id: str
    target_id: str
    type: str  # "requires", "uses", "generalizes", "specializes"
    strength: float = 0.5
    explanation: Optional[str] = None

class DependencyGraph(BaseModel):
    paper_id: str
    nodes: List[str]
    edges: List[Dependency]
    critical_path: List[str] = []

# 5. Tools & Techniques
class ProofTool(BaseModel):
    id: str
    name: str
    description: str
    domain: str
    used_in_theorems: List[str] = []
    related_tools: List[str] = []
    references: List[str] = []

# 6. Analogies & Mappings
class AnalogyMapping(BaseModel):
    source_concept: str
    target_concept: str
    explanation: str
    example_theorem: Optional[str] = None

class Analogy(BaseModel):
    id: str
    source_domain: str
    target_domain: str
    mappings: List[AnalogyMapping] = []
    strength: float = 0.5

# 7. Influences & Historical Context
class Influence(BaseModel):
    influenced_by_id: str
    influenced_theorem_id: str
    type: str  # "inspired", "extends", "generalizes", "analogous"
    explanation: str
    historical_context: Optional[str] = None

class InfluenceTimeline(BaseModel):
    paper_id: str
    influences: List[Influence]

# 8. References & Citations
class Reference(BaseModel):
    id: str
    author: str
    year: int
    title: str
    journal_or_book: str
    cited_in: List[str] = []
    type: str  # "foundational", "technique", "related_result", "historical"
    influence_level: str  # "critical", "important", "supporting"

class HistoricalMap(BaseModel):
    paper_id: str
    references: List[Reference]
    influences: List[Influence]

# 9. Assumptions & Their Status
class Assumption(BaseModel):
    id: str
    statement: str
    introduced_in: str
    used_in: List[str] = []
    status: str  # "active", "eliminated", "relaxed", "conditional"
    elimination_section: Optional[str] = None
    alternative_if_removed: Optional[str] = None

class AssumptionTracker(BaseModel):
    paper_id: str
    assumptions: List[Assumption]

# 10. Open Problems & Conjectures
class OpenProblem(BaseModel):
    id: str
    statement: str
    introduced_by: Optional[str] = None
    related_to_theorem: Optional[str] = None
    importance: str  # "foundational", "important", "interesting"
    potential_impact: str
    status: str  # "open", "solved", "partially_solved"

class OpenProblemsDB(BaseModel):
    paper_id: str
    problems: List[OpenProblem]
    connections: Dict[str, List[str]] = {}

# ============================================================================
# COMPLETE KNOWLEDGE GRAPH
# ============================================================================

class MathematicalPaperKnowledgeGraph(BaseModel):
    """Complete structured representation of a paper as a knowledge graph"""

    paper_id: str
    title: str
    authors: List[str]
    year: int

    # Core entities
    objects: Dict[str, MathematicalObject] = {}
    proofs: Dict[str, Proof] = {}
    equations: Dict[str, Equation] = {}
    tools: Dict[str, ProofTool] = {}
    symbols: List[Symbol] = []

    # Graphs & relationships
    dependency_graph: Optional[DependencyGraph] = None
    influence_timeline: Optional[InfluenceTimeline] = None
    historical_map: Optional[HistoricalMap] = None
    assumption_tracker: Optional[AssumptionTracker] = None

    # Analogies & open problems
    analogies: List[Analogy] = []
    open_problems: Optional[OpenProblemsDB] = None

    # Statistics
    statistics: Dict[str, Any] = {}

    # Visualization hints
    layout_hint: str = "force-directed"
    interactive_elements: List[str] = []

# ============================================================================
# EXAMPLE: PARSE A PAPER INTO KNOWLEDGE GRAPH
# ============================================================================

def create_example_knowledge_graph() -> MathematicalPaperKnowledgeGraph:
    """
    Example: Bettin-Conrey "Approximations to the Riemann Hypothesis"
    """

    kg = MathematicalPaperKnowledgeGraph(
        paper_id="arxiv:1111.0931",
        title="Approximations to the Riemann Hypothesis",
        authors=["Bettin", "Conrey"],
        year=2013,
    )

    # === 1. MATHEMATICAL OBJECTS ===
    kg.objects["theorem_main"] = MathematicalObject(
        id="theorem_main",
        type="theorem",
        name="Period Function Approximation",
        statement="The Riemann hypothesis is equivalent to certain period function bounds",
        section="Section 3",
        assumptions=["assumption_vasyunin"],
        conclusion="M(x) = O(1/log N) weighted sum",
        context="Explicit formulation of RH via Vasyunin cotangent series"
    )

    kg.objects["lemma_contour"] = MathematicalObject(
        id="lemma_contour",
        type="lemma",
        name="Contour Shift Lemma",
        statement="Safe to shift contours under DVP zero-free region",
        section="Section 2",
        conclusion="Perron inversion valid",
    )

    kg.objects["def_period"] = MathematicalObject(
        id="def_period",
        type="definition",
        name="Period Functions",
        statement="Periodic extension with specified growth",
        conclusion="Defined for frequency k, period 1",
    )

    # === 2. PROOFS ===
    kg.proofs["proof_main"] = Proof(
        id="proof_main",
        theorem_id="theorem_main",
        steps=[
            ProofStep(
                index=1,
                description="Fourier expand the cotangent sum",
                justification=["tool_fourier", "tool_reciprocity"],
                equation_refs=["eq_vasyunin_series"]
            ),
            ProofStep(
                index=2,
                description="Shift contours to capture zeros",
                justification=["lemma_contour"],
                equation_refs=["eq_perron_integral"]
            ),
            ProofStep(
                index=3,
                description="Bound the weighted sum",
                justification=["tool_mellin", "theorem_explicit_formula"],
                equation_refs=["eq_bound"]
            )
        ],
        uses_lemmas=["lemma_contour"],
        uses_tools=["tool_fourier", "tool_mellin", "tool_reciprocity"],
        key_insight="Period functions encode cancellation structure",
        length_estimate="8 pages"
    )

    # === 3. EQUATIONS ===
    kg.equations["eq_vasyunin_series"] = Equation(
        id="eq_vasyunin_series",
        latex=r"S_N(x) = \sum_{k=1}^N c_k \cot(\pi k x)",
        meaning="Vasyunin cotangent series",
        context="Section 2, equation (5)",
        related_theorems=["theorem_main"],
        related_definitions=["def_period"]
    )

    # === 4. SYMBOLS ===
    kg.symbols = [
        Symbol(
            latex=r"\Delta",
            name="Möbius function (or residual)",
            meaning="Arithmetic function or error term",
            first_appearance="Section 1",
            uses=["theorem_main", "lemma_contour"],
            related_symbols=[r"\mu", r"\lambda"]
        ),
        Symbol(
            latex=r"S_N",
            name="Weighted cotangent sum",
            meaning="Sum of period functions",
            uses=["eq_vasyunin_series", "theorem_main"],
        )
    ]

    # === 5. TOOLS ===
    kg.tools["tool_fourier"] = ProofTool(
        id="tool_fourier",
        name="Fourier Analysis",
        description="Orthonormal decomposition in GL(2)",
        domain="Harmonic Analysis",
        used_in_theorems=["theorem_main"],
        related_tools=["tool_reciprocity", "tool_mellin"],
        references=["ref_whittaker_watson", "ref_stein_weiss"]
    )

    kg.tools["tool_mellin"] = ProofTool(
        id="tool_mellin",
        name="Mellin Transform",
        description="Integral transform for asymptotic analysis",
        domain="Complex Analysis",
        used_in_theorems=["theorem_main"],
        references=["ref_iwaniec_kowalski"]
    )

    # === 6. DEPENDENCIES ===
    kg.dependency_graph = DependencyGraph(
        paper_id="arxiv:1111.0931",
        nodes=["theorem_main", "lemma_contour", "def_period"],
        edges=[
            Dependency(
                source_id="theorem_main",
                target_id="lemma_contour",
                type="requires",
                strength=0.95,
                explanation="Contour shift is essential step"
            ),
            Dependency(
                source_id="theorem_main",
                target_id="def_period",
                type="requires",
                strength=0.90,
                explanation="Period functions are central object"
            )
        ],
        critical_path=["def_period", "lemma_contour", "theorem_main"]
    )

    # === 7. ANALOGIES ===
    kg.analogies = [
        Analogy(
            id="dict_ag_nt",
            source_domain="Spectral Theory",
            target_domain="Number Theory",
            mappings=[
                AnalogyMapping(
                    source_concept="Eigenvalues of operator",
                    target_concept="Zeros of ζ(s)",
                    explanation="GUE distribution predicts zero spacing",
                    example_theorem="theorem_main"
                )
            ],
            strength=0.7
        )
    ]

    # === 8. INFLUENCES ===
    kg.influence_timeline = InfluenceTimeline(
        paper_id="arxiv:1111.0931",
        influences=[
            Influence(
                influenced_by_id="ref_vasyunin_1999",
                influenced_theorem_id="theorem_main",
                type="extends",
                explanation="Builds on Vasyunin's cotangent identity",
                historical_context="Direct continuation of 1999 work"
            ),
            Influence(
                influenced_by_id="ref_baez_duarte_2003",
                influenced_theorem_id="theorem_main",
                type="inspired",
                explanation="BBLS chain provides methodology"
            )
        ]
    )

    kg.historical_map = HistoricalMap(
        paper_id="arxiv:1111.0931",
        references=[
            Reference(
                id="ref_vasyunin_1999",
                author="Vasyunin",
                year=1999,
                title="Cotangent Sums and the Riemann Hypothesis",
                journal_or_book="Unpublished",
                cited_in=["theorem_main"],
                type="foundational",
                influence_level="critical"
            ),
            Reference(
                id="ref_baez_duarte_2003",
                author="Báez-Duarte",
                year=2003,
                title="New Weighted Mean Values with Power Sums",
                journal_or_book="Journal of Number Theory",
                cited_in=["theorem_main", "lemma_contour"],
                type="technique",
                influence_level="important"
            )
        ],
        influences=[
            Influence(
                influenced_by_id="ref_vasyunin_1999",
                influenced_theorem_id="theorem_main",
                type="extends",
                explanation="Explicit cotangent series",
            )
        ]
    )

    # === 9. ASSUMPTIONS ===
    kg.assumption_tracker = AssumptionTracker(
        paper_id="arxiv:1111.0931",
        assumptions=[
            Assumption(
                id="assumption_vasyunin",
                statement="Vasyunin identity holds (period functional equations)",
                introduced_in="Section 1",
                used_in=["theorem_main", "lemma_contour"],
                status="active",
                alternative_if_removed="Must develop reciprocity machinery independently"
            ),
            Assumption(
                id="assumption_dvp",
                statement="De la Vallée Poussin zero-free region",
                introduced_in="Section 2",
                used_in=["lemma_contour"],
                status="active",
                alternative_if_removed="Cannot shift contours safely"
            )
        ]
    )

    # === 10. OPEN PROBLEMS ===
    kg.open_problems = OpenProblemsDB(
        paper_id="arxiv:1111.0931",
        problems=[
            OpenProblem(
                id="problem_pointwise",
                statement="Can bounds be made pointwise instead of aggregate?",
                related_to_theorem="theorem_main",
                importance="important",
                potential_impact="Would strengthen approximation significantly",
                status="open"
            ),
            OpenProblem(
                id="problem_quadratic",
                statement="Characterize quadratic Möbius-Vasyunin interactions",
                importance="foundational",
                potential_impact="Would complete understanding of cancellation",
                status="open"
            )
        ],
        connections={
            "theorem_main": ["problem_pointwise", "problem_quadratic"],
            "section_3": ["problem_quadratic"]
        }
    )

    # === STATISTICS ===
    kg.statistics = {
        "total_theorems": 1,
        "total_lemmas": 1,
        "total_definitions": 1,
        "total_equations": 1,
        "total_symbols": 2,
        "total_tools": 2,
        "total_references": 2,
        "total_assumptions": 2,
        "open_problems_count": 2,
        "proof_steps": 3,
        "dependency_depth": 2,
        "most_used_tool": "tool_fourier",
        "critical_path_length": 3
    }

    kg.interactive_elements = [
        "theorem_main",
        "lemma_contour",
        "proof_main",
        "dependency_graph",
        "eq_vasyunin_series",
        "tool_fourier",
        "problem_pointwise"
    ]

    return kg

# ============================================================================
# EXPORT FUNCTIONS
# ============================================================================

def export_to_jsonld(kg: MathematicalPaperKnowledgeGraph) -> Dict[str, Any]:
    """Export knowledge graph to JSON-LD format"""
    return {
        "@context": {
            "@vocab": "https://example.org/mathematics#",
            "rdf": "http://www.w3.org/1999/02/22-rdf-syntax-ns#",
        },
        "id": f"paper:{kg.paper_id}",
        "title": kg.title,
        "authors": kg.authors,
        "year": kg.year,
        "objects": list(kg.objects.values()),
        "proofs": list(kg.proofs.values()),
        "dependencies": kg.dependency_graph.edges if kg.dependency_graph else [],
        "open_problems": kg.open_problems.problems if kg.open_problems else []
    }

def export_to_neo4j_cypher(kg: MathematicalPaperKnowledgeGraph) -> List[str]:
    """Generate Cypher queries for Neo4j import"""
    queries = []

    # Create theorem nodes
    for obj_id, obj in kg.objects.items():
        queries.append(
            f'CREATE (:{obj.type.upper()} {{id:"{obj_id}", name:"{obj.name}", '
            f'statement:"{obj.statement}"}})'
        )

    # Create dependency edges
    if kg.dependency_graph:
        for edge in kg.dependency_graph.edges:
            queries.append(
                f'MATCH (a {{id:"{edge.source_id}"}}), (b {{id:"{edge.target_id}"}}) '
                f'CREATE (a)-[:{edge.type.upper()}]->(b)'
            )

    return queries

# ============================================================================
# MAIN: Example Usage
# ============================================================================

if __name__ == "__main__":
    print("Generating Knowledge Graph for Bettin-Conrey 2013...")
    kg = create_example_knowledge_graph()

    print(f"\n✅ Knowledge Graph Built: {kg.paper_id}")
    print(f"   Theorems: {len(kg.objects)}")
    print(f"   Proofs: {len(kg.proofs)}")
    print(f"   Equations: {len(kg.equations)}")
    print(f"   Tools: {len(kg.tools)}")
    print(f"   Symbols: {len(kg.symbols)}")
    print(f"   Open Problems: {len(kg.open_problems.problems) if kg.open_problems else 0}")

    # Export
    jsonld = export_to_jsonld(kg)
    with open("/Users/xavierfresquet/Documents/Musicologie/CAPTAL-LAB/4-MISC/math/riemann/example_knowledge_graph.json", "w") as f:
        json.dump(jsonld, f, indent=2, default=str)

    print(f"\n💾 Exported to JSON-LD")
    print(f"📊 Statistics: {kg.statistics}")
