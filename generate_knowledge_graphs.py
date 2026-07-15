#!/usr/bin/env python3
"""
Knowledge Graph Generator for RH Corpus
Extracts 10 knowledge dimensions from 30 papers and generates visualizations
"""

import json
import os
from pathlib import Path
from typing import Dict, List, Any, Optional
from datetime import datetime
from pydantic import BaseModel

# ============================================================================
# PYDANTIC MODELS (from parser, simplified for corpus)
# ============================================================================

class MathematicalObject(BaseModel):
    id: str
    type: str
    name: str
    statement: str
    section: Optional[str] = None
    assumptions: List[str] = []
    conclusion: str
    context: Optional[str] = None

class OpenProblem(BaseModel):
    id: str
    statement: str
    importance: str
    status: str

class ProofTool(BaseModel):
    id: str
    name: str
    description: str
    domain: str
    used_in_theorems: List[str] = []

class Dependency(BaseModel):
    source_id: str
    target_id: str
    type: str
    strength: float = 0.5
    explanation: Optional[str] = None

class KnowledgeGraph(BaseModel):
    paper_id: str
    title: str
    authors: List[str]
    year: int
    phase: str
    contributions: List[str] = []
    key_concepts: List[str] = []
    related_papers: List[str] = []
    tools_used: List[str] = []
    key_theorems: List[Dict[str, str]] = []
    open_problems: List[str] = []
    statistics: Dict[str, Any] = {}

# ============================================================================
# LOAD CORPUS DATABASE
# ============================================================================

def load_corpus() -> List[Dict[str, Any]]:
    """Load the complete RH corpus"""
    corpus_path = Path("/Users/xavierfresquet/Documents/Musicologie/CAPTAL-LAB/4-MISC/math/riemann/rh_corpus_database_complete.json")
    with open(corpus_path, 'r') as f:
        data = json.load(f)
    return data.get('articles', [])

# ============================================================================
# EXTRACT KNOWLEDGE FROM PAPER METADATA
# ============================================================================

def extract_phase(role_in_project: str) -> str:
    """Map role_in_project to phase name"""
    role_map = {
        "H13": "Classical Foundation",
        "H14": "Quantitative Bounds",
        "H15": "Cancellation Structure",
        "General": "General Theory",
        "Routes": "Alternative Routes"
    }
    return role_map.get(role_in_project, "General Theory")

def extract_key_concepts(tags: List[str], title: str) -> List[str]:
    """Extract key concepts from tags and title"""
    # Map tags to readable concepts
    concept_map = {
        "möbius": "Möbius Functions",
        "vasyunin": "Vasyunin Cotangent Sums",
        "period": "Period Functions",
        "zeta": "Zeta Functions",
        "mellin": "Mellin Transform",
        "fourier": "Fourier Analysis",
        "approximations": "RH Approximations",
        "nyman-beurling": "Nyman-Beurling Criterion",
        "functional": "Functional Analysis",
        "spectral": "Spectral Methods",
    }

    concepts = []
    for tag in tags:
        if tag in concept_map:
            concepts.append(concept_map[tag])

    # Add concepts from title
    title_lower = title.lower()
    if "approximation" in title_lower or "approximations" in title_lower:
        concepts.append("RH Approximations")
    if "zeta" in title_lower:
        concepts.append("Zeta Functions")
    if "trace" in title_lower:
        concepts.append("Trace Formula")

    return list(set(concepts))

def create_knowledge_graph_from_paper(paper: Dict[str, Any], all_papers: List[Dict]) -> KnowledgeGraph:
    """Create a knowledge graph from paper metadata"""

    # Find related papers (same phase or cited/citing)
    phase = paper.get('role_in_project', 'General')
    related = [p['id'] for p in all_papers
               if p.get('role_in_project') == phase and p['id'] != paper['id']][:3]

    kg = KnowledgeGraph(
        paper_id=paper['id'],
        title=paper['title'],
        authors=[a['name'] for a in paper.get('authors', [])],
        year=paper['year'],
        phase=extract_phase(phase),
        contributions=[],  # Will be extracted from title/tags
        key_concepts=extract_key_concepts(paper.get('tags', []), paper['title']),
        related_papers=related,
        tools_used=extract_tools_from_tags(paper.get('tags', [])),
        statistics={
            "relevance_score": paper.get('relevance_score', 0.5),
            "year": paper['year'],
            "authors_count": len(paper.get('authors', [])),
        }
    )

    return kg

def extract_tools_from_tags(tags: List[str]) -> List[str]:
    """Extract mathematical tools from tags"""
    tool_map = {
        "fourier": "Fourier Analysis",
        "mellin": "Mellin Transform",
        "zeta": "Zeta Functions",
        "explicit": "Explicit Formulas",
        "contour": "Contour Integration",
        "residue": "Residue Calculus",
    }

    tools = []
    for tag in tags:
        if tag in tool_map:
            tools.append(tool_map[tag])
    return list(set(tools))

# ============================================================================
# GENERATE VISUALIZATIONS
# ============================================================================

def sanitize_filename(paper_id: str) -> str:
    """Sanitize paper ID for use as filename"""
    return paper_id.replace('/', '_')

def generate_paper_knowledge_graph_html(kg: KnowledgeGraph, paper_id: str) -> str:
    """Generate a simple HTML page showing the knowledge graph for a paper"""

    html = f"""<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="utf-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Knowledge Graph: {kg.title}</title>
    <style>
        * {{ margin: 0; padding: 0; box-sizing: border-box; }}
        body {{ font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, sans-serif; background: #f5f5f5; padding: 2rem; }}
        .container {{ max-width: 1000px; margin: 0 auto; background: white; border-radius: 8px; padding: 2rem; box-shadow: 0 2px 8px rgba(0,0,0,0.1); }}
        header {{ margin-bottom: 2rem; border-bottom: 2px solid #3b82f6; padding-bottom: 1rem; }}
        h1 {{ color: #1f2937; margin-bottom: 0.5rem; }}
        .meta {{ color: #666; font-size: 0.95rem; }}
        .section {{ margin: 1.5rem 0; }}
        .section h2 {{ color: #1f2937; font-size: 1.3rem; margin-bottom: 0.75rem; border-left: 4px solid #3b82f6; padding-left: 0.75rem; }}
        .tag {{ display: inline-block; background: #e0f2fe; color: #0369a1; padding: 0.25rem 0.75rem; border-radius: 4px; margin: 0.25rem 0.25rem 0.25rem 0; font-size: 0.85rem; }}
        .stat {{ display: inline-block; margin-right: 1.5rem; margin-bottom: 0.5rem; }}
        .stat-label {{ color: #666; font-size: 0.9rem; }}
        .stat-value {{ color: #1f2937; font-weight: bold; }}
        .concept-grid {{ display: grid; grid-template-columns: repeat(auto-fill, minmax(150px, 1fr)); gap: 0.75rem; }}
        .concept-box {{ background: #f0f9ff; border: 1px solid #bfdbfe; border-radius: 6px; padding: 0.75rem; text-align: center; color: #0369a1; font-size: 0.9rem; }}
        .tool-list {{ display: grid; grid-template-columns: repeat(auto-fill, minmax(180px, 1fr)); gap: 0.75rem; }}
        .tool-item {{ background: #fef3c7; border: 1px solid #fde68a; border-radius: 6px; padding: 0.75rem; color: #92400e; font-size: 0.9rem; }}
        .related {{ background: #f3e8ff; border-left: 4px solid #a855f7; padding: 0.75rem; border-radius: 4px; margin: 0.5rem 0; }}
        .back-link {{ color: #3b82f6; text-decoration: none; margin-bottom: 1rem; display: inline-block; }}
        .back-link:hover {{ text-decoration: underline; }}
    </style>
</head>
<body>
    <div class="container">
        <a href="corpus.html" class="back-link">← Back to Corpus</a>

        <header>
            <h1>{kg.title}</h1>
            <div class="meta">
                <div><strong>Paper ID:</strong> {kg.paper_id}</div>
                <div><strong>Authors:</strong> {', '.join(kg.authors[:3])}{'...' if len(kg.authors) > 3 else ''}</div>
                <div><strong>Year:</strong> {kg.year} | <strong>Phase:</strong> <span style="color: #0369a1; font-weight: bold;">{kg.phase}</span></div>
            </div>
        </header>

        <div class="section">
            <h2>📊 Key Concepts</h2>
            <div class="concept-grid">
                {''.join(f'<div class="concept-box">{concept}</div>' for concept in kg.key_concepts)}
            </div>
        </div>

        <div class="section">
            <h2>🔧 Mathematical Tools</h2>
            <div class="tool-list">
                {''.join(f'<div class="tool-item">{tool}</div>' for tool in kg.tools_used)}
            </div>
        </div>

        <div class="section">
            <h2>📈 Statistics</h2>
            <div>
                <div class="stat"><span class="stat-label">Relevance Score:</span> <span class="stat-value">{kg.statistics.get('relevance_score', 0.0):.2f}</span></div>
                <div class="stat"><span class="stat-label">Authors:</span> <span class="stat-value">{kg.statistics.get('authors_count', 0)}</span></div>
            </div>
        </div>

        <div class="section">
            <h2>🔗 Related Papers in Corpus</h2>
            {''.join(f'<div class="related">📄 Paper ID: <code>{pid}</code></div>' for pid in kg.related_papers)}
            {f'<div class="related">No related papers in same phase</div>' if not kg.related_papers else ''}
        </div>

        <div style="margin-top: 2rem; padding-top: 1rem; border-top: 1px solid #e5e7eb; color: #666; font-size: 0.9rem;">
            <p>Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')} | <a href="about.html" style="color: #3b82f6;">About this project</a></p>
        </div>
    </div>
</body>
</html>"""

    return html

# ============================================================================
# GENERATE CORPUS-WIDE KNOWLEDGE EXPLORER
# ============================================================================

def generate_knowledge_explorer_html(kgs: Dict[str, KnowledgeGraph]) -> str:
    """Generate interactive knowledge graph explorer page"""

    # Count papers by phase
    phases = {}
    for kg in kgs.values():
        phase = kg.phase
        if phase not in phases:
            phases[phase] = {"count": 0, "papers": []}
        phases[phase]["count"] += 1
        phases[phase]["papers"].append(kg)

    # Collect all unique concepts
    all_concepts = set()
    for kg in kgs.values():
        all_concepts.update(kg.key_concepts)

    html = f"""<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="utf-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Knowledge Graph Explorer</title>
    <style>
        * {{ margin: 0; padding: 0; box-sizing: border-box; }}
        body {{ font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, sans-serif; background: #f5f5f5; }}

        header {{
            display: flex;
            align-items: center;
            justify-content: space-between;
            padding: 2rem;
            background: white;
            border-bottom: 2px solid #3b82f6;
            margin-bottom: 0;
        }}

        header img {{ height: 60px; margin-right: 1rem; }}
        h1 {{ color: #1f2937; }}

        nav {{
            background: white;
            padding: 1rem 2rem;
            border-bottom: 1px solid #e5e7eb;
            margin-bottom: 2rem;
        }}

        nav ul {{
            list-style: none;
            display: flex;
            gap: 2rem;
            max-width: 1200px;
            margin: 0 auto;
        }}

        nav a {{
            color: #1f2937;
            text-decoration: none;
            font-weight: 500;
        }}

        nav a:hover {{ color: #3b82f6; }}

        main {{
            max-width: 1200px;
            margin: 0 auto;
            padding: 0 2rem;
        }}

        .explorer-grid {{
            display: grid;
            grid-template-columns: 1fr 1fr;
            gap: 2rem;
        }}

        .phase-section {{
            background: white;
            border-radius: 8px;
            padding: 1.5rem;
            box-shadow: 0 2px 4px rgba(0,0,0,0.1);
        }}

        .phase-header {{
            font-size: 1.3rem;
            font-weight: bold;
            color: #1f2937;
            margin-bottom: 1rem;
            padding-bottom: 0.5rem;
            border-bottom: 2px solid #3b82f6;
        }}

        .paper-link {{
            display: block;
            padding: 0.75rem;
            margin: 0.5rem 0;
            background: #f0f9ff;
            border-left: 4px solid #3b82f6;
            border-radius: 4px;
            text-decoration: none;
            color: #0369a1;
            font-size: 0.9rem;
        }}

        .paper-link:hover {{
            background: #e0f2fe;
        }}

        .concept-cloud {{
            display: flex;
            flex-wrap: wrap;
            gap: 0.5rem;
            margin-top: 2rem;
            padding: 1.5rem;
            background: #f9fafb;
            border-radius: 8px;
        }}

        .concept-tag {{
            background: #dbeafe;
            color: #1e40af;
            padding: 0.4rem 0.8rem;
            border-radius: 20px;
            font-size: 0.85rem;
        }}

        footer {{
            margin-top: 3rem;
            padding: 2rem;
            background: white;
            text-align: center;
            color: #666;
            border-top: 1px solid #e5e7eb;
        }}
    </style>
</head>
<body>
    <header>
        <div>
            <h1>🔗 Knowledge Graph Explorer</h1>
            <p style="color: #666;">Interactive view of the RH corpus by phase and mathematical concepts</p>
        </div>
    </header>

    <nav>
        <ul>
            <li><a href="index.html">Home</a></li>
            <li><a href="intro.html">Vision & Method</a></li>
            <li><a href="corpus.html">📚 Complete Corpus</a></li>
            <li><a href="mathematicians.html">👥 Mathematicians</a></li>
            <li><a href="visualizations.html">📊 Visualizations</a></li>
            <li><a href="about.html">About</a></li>
        </ul>
    </nav>

    <main>
        <div class="explorer-grid">
            {''.join(f'''
            <div class="phase-section">
                <div class="phase-header">🔵 {phase}</div>
                <p style="color: #666; font-size: 0.9rem; margin-bottom: 0.75rem;">{info["count"]} papers</p>
                {''.join(f'<a href="kg_{sanitize_filename(kg.paper_id)}.html" class="paper-link">{kg.title[:50]}...</a>'
                         if len(kg.title) > 50
                         else f'<a href="kg_{sanitize_filename(kg.paper_id)}.html" class="paper-link">{kg.title}</a>'
                         for kg in info["papers"][:5])}
            </div>
            ''' for phase, info in phases.items())}
        </div>

        <div style="margin-top: 2rem; background: white; border-radius: 8px; padding: 1.5rem; box-shadow: 0 2px 4px rgba(0,0,0,0.1);">
            <h2 style="margin-bottom: 1rem;">🧮 All Mathematical Concepts</h2>
            <div class="concept-cloud">
                {''.join(f'<div class="concept-tag">{concept}</div>' for concept in sorted(all_concepts))}
            </div>
        </div>
    </main>

    <footer>
        <p><strong>RH Corpus Knowledge Graphs</strong> — {len(kgs)} papers analyzed</p>
        <p>Generated {datetime.now().strftime('%Y-%m-%d')} | <a href="about.html" style="color: #3b82f6;">Learn more</a></p>
    </footer>
</body>
</html>"""

    return html

# ============================================================================
# MAIN PIPELINE
# ============================================================================

def main():
    print("🔄 Generating Knowledge Graphs for RH Corpus...")
    print("=" * 70)

    # Load corpus
    papers = load_corpus()
    print(f"✅ Loaded {len(papers)} papers")

    # Generate knowledge graphs
    kgs = {}
    for paper in papers:
        kg = create_knowledge_graph_from_paper(paper, papers)
        kgs[paper['id']] = kg

    print(f"✅ Created {len(kgs)} knowledge graphs")

    # Generate HTML files
    output_dir = Path("/Users/xavierfresquet/Documents/Musicologie/CAPTAL-LAB/4-MISC/math/riemann/doc/html")
    output_dir.mkdir(parents=True, exist_ok=True)

    # Generate per-paper knowledge graph pages
    for paper_id, kg in kgs.items():
        html = generate_paper_knowledge_graph_html(kg, paper_id)
        safe_id = sanitize_filename(paper_id)
        output_file = output_dir / f"kg_{safe_id}.html"
        output_file.write_text(html)
        print(f"  📄 {paper_id}")

    print(f"✅ Generated {len(kgs)} paper knowledge graph pages")

    # Generate explorer page
    explorer_html = generate_knowledge_explorer_html(kgs)
    explorer_file = output_dir / "knowledge-explorer.html"
    explorer_file.write_text(explorer_html)
    print(f"✅ Generated knowledge graph explorer")

    # Generate JSON export
    json_export = {
        "generated": datetime.now().isoformat(),
        "total_papers": len(kgs),
        "knowledge_graphs": {pid: kg.dict() for pid, kg in kgs.items()}
    }

    json_file = output_dir / "knowledge_graphs.json"
    with open(json_file, 'w') as f:
        json.dump(json_export, f, indent=2, default=str)

    print(f"✅ Generated JSON export")
    print("=" * 70)
    print("📊 Summary:")
    print(f"   Total papers: {len(kgs)}")

    phases = {}
    for kg in kgs.values():
        phase = kg.phase
        phases[phase] = phases.get(phase, 0) + 1

    for phase, count in sorted(phases.items()):
        print(f"   - {phase}: {count} papers")

    print(f"\n✅ All knowledge graphs generated!")
    print(f"📍 Location: {output_dir}")
    print(f"🌐 Visit: doc/html/knowledge-explorer.html")

if __name__ == "__main__":
    main()
