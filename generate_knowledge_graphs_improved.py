#!/usr/bin/env python3
"""
Enhanced Knowledge Graph Generator
Extracts richer metadata from corpus with improved concept/tool detection
"""

import json
from pathlib import Path
from typing import List, Dict, Any, Set
from datetime import datetime

# ============================================================================
# ENHANCED CONCEPT & TOOL EXTRACTION
# ============================================================================

CONCEPT_MAP = {
    "möbius": "Möbius Functions",
    "mobius": "Möbius Functions",
    "vasyunin": "Vasyunin Cotangent Sums",
    "cotangent": "Cotangent Sums",
    "period": "Period Functions",
    "zeta": "Zeta Functions",
    "mellin": "Mellin Transform",
    "fourier": "Fourier Analysis",
    "approximation": "RH Approximations",
    "nyman": "Nyman-Beurling Criterion",
    "beurling": "Nyman-Beurling Criterion",
    "functional": "Functional Analysis",
    "spectral": "Spectral Methods",
    "trace": "Trace Formula",
    "reciprocity": "Reciprocity Relations",
    "dirichlet": "Dirichlet Polynomials",
    "explicit": "Explicit Formulas",
    "contour": "Contour Shifting",
    "borel": "Borel-Jensen Factorization",
    "jensen": "Borel-Jensen Factorization",
    "perron": "Perron Inversion",
    "correlation": "Correlation & Cancellation",
    "cancellation": "Möbius Cancellation",
    "dvp": "De la Vallée Poussin",
    "zero-free": "Zero-Free Regions",
    "eigenvalue": "Eigenvalue Methods",
    "random matrix": "Random Matrix Theory",
    "gue": "GUE / Spacing Distribution",
    "distribution": "Spacing Distributions",
    "hilbert": "Hilbert Space Methods",
    "pólya": "Hilbert-Pólya Conjecture",
    "polya": "Hilbert-Pólya Conjecture",
}

TOOL_MAP = {
    "fourier": "Fourier Analysis",
    "mellin": "Mellin Transform",
    "zeta": "Zeta Function Methods",
    "contour": "Contour Integration",
    "residue": "Residue Calculus",
    "explicit": "Explicit Formulas",
    "dirichlet": "Dirichlet Series",
    "poisson": "Poisson Summation",
    "reciprocity": "Reciprocity Formulas",
    "voronoi": "Voronoi Summation",
    "large sieve": "Large Sieve",
    "dyadic": "Dyadic Decomposition",
    "stationary phase": "Stationary Phase",
    "kloosterman": "Kloosterman Sums",
    "character": "Dirichlet Characters",
}

CONCEPT_KEYWORDS = [
    "möbius", "vasyunin", "cotangent", "period function", "zeta",
    "mellin", "fourier", "approximation", "nyman", "beurling",
    "functional", "spectral", "trace formula", "reciprocity",
    "dirichlet", "explicit formula", "contour", "borel", "jensen",
    "perron", "correlation", "cancellation", "dvp", "zero-free",
    "eigenvalue", "random matrix", "hilbert", "pólya", "eigenvector"
]

def extract_concepts_enhanced(title: str, tags: List[str], role: str, year: int) -> List[str]:
    """Enhanced concept extraction using title, tags, role, and date"""
    concepts: Set[str] = set()

    # From tags
    for tag in tags:
        tag_lower = tag.lower()
        if tag_lower in CONCEPT_MAP:
            concepts.add(CONCEPT_MAP[tag_lower])
        elif "möbius" in tag_lower or "mobius" in tag_lower:
            concepts.add("Möbius Functions")
        elif "period" in tag_lower:
            concepts.add("Period Functions")
        elif "zeta" in tag_lower:
            concepts.add("Zeta Functions")

    # From title
    title_lower = title.lower()
    for keyword in CONCEPT_KEYWORDS:
        if keyword in title_lower:
            concept = CONCEPT_MAP.get(keyword, keyword.title())
            concepts.add(concept)

    # From role/phase
    if role == "H13":
        concepts.update(["Vasyunin Cotangent Sums", "Period Functions", "Explicit Formulas"])
    elif role == "H14":
        concepts.update(["Möbius Functions", "Quantitative Bounds", "Mellin Transform", "Contour Shifting"])
    elif role == "H15":
        concepts.update(["Möbius Cancellation", "Bilinear Estimates", "Fourier Analysis"])

    # From date (older = classical foundations)
    if year < 1950:
        concepts.add("Classical Analytic Number Theory")
    elif year < 2000:
        concepts.add("Modern Techniques")
    else:
        concepts.add("Contemporary Research")

    # Fallback: ensure non-empty
    if not concepts:
        concepts.add("Riemann Hypothesis")
        concepts.add("Analytic Number Theory")

    return sorted(list(concepts))

def extract_tools_enhanced(tags: List[str], title: str) -> List[str]:
    """Enhanced tool extraction"""
    tools: Set[str] = set()

    combined_text = (title + " " + " ".join(tags)).lower()

    for keyword, tool_name in TOOL_MAP.items():
        if keyword in combined_text:
            tools.add(tool_name)

    # Default tools based on concepts
    if "mellin" in combined_text or "fourier" in combined_text:
        tools.add("Integral Transforms")
    if "contour" in combined_text or "zeta" in combined_text:
        tools.add("Complex Analysis")
    if "dirichlet" in combined_text or "character" in combined_text:
        tools.add("Analytic Number Theory")

    # Fallback: ensure non-empty
    if not tools:
        if "fourier" in combined_text or "analysis" in combined_text:
            tools.add("Harmonic Analysis")
        else:
            tools.add("Complex Analysis")
            tools.add("Number-Theoretic Methods")

    return sorted(list(tools))

# ============================================================================
# IMPROVED HTML GENERATION
# ============================================================================

def generate_paper_knowledge_graph_html_improved(kg: Dict[str, Any], paper_id: str) -> str:
    """Generate improved HTML with Extraction Details section first"""

    concepts = kg.get('key_concepts', [])
    tools = kg.get('tools_used', [])

    # Ensure non-empty
    if not concepts:
        concepts = ["Riemann Hypothesis", "Analytic Number Theory"]
    if not tools:
        tools = ["Complex Analysis"]

    # Format related papers
    related_html = ""
    for pid in kg.get('related_papers', [])[:5]:
        related_html += f'<div class="extraction-item">📄 <code>{pid}</code></div>'
    if not related_html:
        related_html = '<div class="extraction-item" style="color: #999;">No related papers in same phase</div>'

    html = f"""<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="utf-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Knowledge Graph: {kg['title']}</title>
    <style>
        * {{ margin: 0; padding: 0; box-sizing: border-box; }}
        body {{ font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, sans-serif; background: #f5f5f5; padding: 2rem; }}
        .container {{ max-width: 1200px; margin: 0 auto; background: white; border-radius: 8px; padding: 2rem; box-shadow: 0 2px 8px rgba(0,0,0,0.1); }}

        header {{ margin-bottom: 2rem; padding-bottom: 1.5rem; border-bottom: 3px solid #3b82f6; }}
        h1 {{ color: #1f2937; margin-bottom: 0.75rem; font-size: 1.8rem; }}
        .meta {{ display: grid; grid-template-columns: repeat(auto-fit, minmax(200px, 1fr)); gap: 1rem; }}
        .meta-item {{ color: #666; }}
        .meta-item strong {{ color: #1f2937; }}

        .extraction-section {{ background: linear-gradient(135deg, #f0f9ff 0%, #f3e8ff 100%); padding: 2rem; border-radius: 8px; margin-bottom: 2rem; border: 2px solid #e0f2fe; }}
        .extraction-section h2 {{ color: #0369a1; margin-bottom: 1.5rem; font-size: 1.3rem; border-left: 4px solid #3b82f6; padding-left: 0.75rem; }}

        .extraction-grid {{ display: grid; grid-template-columns: repeat(auto-fit, minmax(250px, 1fr)); gap: 1.5rem; }}
        .extraction-box {{ background: white; padding: 1.25rem; border-radius: 6px; box-shadow: 0 1px 4px rgba(0,0,0,0.05); }}
        .extraction-box h3 {{ color: #1f2937; font-size: 1.1rem; margin-bottom: 0.75rem; display: flex; align-items: center; gap: 0.5rem; }}

        .concept-grid {{ display: grid; grid-template-columns: repeat(auto-fill, minmax(140px, 1fr)); gap: 0.5rem; }}
        .concept-tag {{ background: #dbeafe; color: #0369a1; padding: 0.5rem 0.75rem; border-radius: 4px; font-size: 0.9rem; text-align: center; border: 1px solid #bfdbfe; }}

        .tool-grid {{ display: grid; grid-template-columns: repeat(auto-fill, minmax(160px, 1fr)); gap: 0.5rem; }}
        .tool-tag {{ background: #fef3c7; color: #92400e; padding: 0.5rem 0.75rem; border-radius: 4px; font-size: 0.9rem; text-align: center; border: 1px solid #fde68a; }}

        .item-list {{ display: flex; flex-direction: column; gap: 0.5rem; }}
        .extraction-item {{ background: #f3e8ff; border-left: 3px solid #a855f7; padding: 0.75rem; border-radius: 4px; color: #6b21a8; font-size: 0.95rem; }}
        .extraction-item code {{ background: rgba(0,0,0,0.05); padding: 0.2rem 0.4rem; border-radius: 2px; }}

        .section {{ margin: 2rem 0; }}
        .section h2 {{ color: #1f2937; font-size: 1.3rem; margin-bottom: 0.75rem; border-left: 4px solid #3b82f6; padding-left: 0.75rem; }}

        .stat {{ display: inline-block; margin-right: 2rem; margin-bottom: 0.75rem; }}
        .stat-label {{ color: #666; font-size: 0.9rem; }}
        .stat-value {{ color: #1f2937; font-weight: bold; }}

        .back-link {{ color: #3b82f6; text-decoration: none; margin-bottom: 1rem; display: inline-block; }}
        .back-link:hover {{ text-decoration: underline; }}

        footer {{ margin-top: 2rem; padding-top: 1rem; border-top: 1px solid #e5e7eb; color: #666; font-size: 0.9rem; }}
    </style>
</head>
<body>
    <div class="container">
        <a href="corpus.html" class="back-link">← Back to Corpus</a>

        <header>
            <h1>{kg['title']}</h1>
            <div class="meta">
                <div class="meta-item"><strong>Paper ID:</strong> {paper_id}</div>
                <div class="meta-item"><strong>Authors:</strong> {', '.join(kg['authors'][:3])}{'...' if len(kg['authors']) > 3 else ''}</div>
                <div class="meta-item"><strong>Year:</strong> {kg['year']}</div>
                <div class="meta-item"><strong>Phase:</strong> <span style="color: #0369a1; font-weight: bold;">{kg['phase']}</span></div>
            </div>
        </header>

        <div class="extraction-section">
            <h2>📊 Extraction Details</h2>
            <div class="extraction-grid">
                <div class="extraction-box">
                    <h3>🧮 Key Concepts ({len(concepts)})</h3>
                    <div class="concept-grid">
                        {"".join(f'<div class="concept-tag">{c}</div>' for c in concepts)}
                    </div>
                </div>

                <div class="extraction-box">
                    <h3>🔧 Mathematical Tools ({len(tools)})</h3>
                    <div class="tool-grid">
                        {"".join(f'<div class="tool-tag">{t}</div>' for t in tools)}
                    </div>
                </div>

                <div class="extraction-box">
                    <h3>🔗 Related Papers ({len(kg.get('related_papers', []))})</h3>
                    <div class="item-list">
                        {related_html}
                    </div>
                </div>
            </div>
        </div>

        <div class="section">
            <h2>📈 Publication Metrics</h2>
            <div>
                <div class="stat"><span class="stat-label">Relevance Score:</span> <span class="stat-value">{kg['statistics'].get('relevance_score', 0.5):.2f}</span></div>
                <div class="stat"><span class="stat-label">Authors:</span> <span class="stat-value">{kg['statistics'].get('authors_count', 0)}</span></div>
                <div class="stat"><span class="stat-label">Publication Year:</span> <span class="stat-value">{kg['year']}</span></div>
            </div>
        </div>

        <footer>
            <p>Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')} | <a href="about.html" style="color: #3b82f6;">About this project</a> | <a href="knowledge-explorer.html" style="color: #3b82f6;">Knowledge Graph Explorer</a></p>
        </footer>
    </div>
</body>
</html>"""

    return html

# ============================================================================
# MAIN PIPELINE
# ============================================================================

def load_corpus() -> List[Dict[str, Any]]:
    """Load the complete RH corpus"""
    corpus_path = Path("/Users/xavierfresquet/Documents/Musicologie/CAPTAL-LAB/4-MISC/math/riemann/doc/html/rh_corpus_database_complete.json")
    with open(corpus_path, 'r') as f:
        data = json.load(f)
    return data.get('articles', [])

def main():
    print("🔄 Generating Enhanced Knowledge Graphs...")
    print("=" * 70)

    papers = load_corpus()
    print(f"✅ Loaded {len(papers)} papers")

    output_dir = Path("/Users/xavierfresquet/Documents/Musicologie/CAPTAL-LAB/4-MISC/math/riemann/doc/html")

    # Map role to phase names
    role_to_phase = {
        "H13": "Classical Foundation",
        "H14": "Quantitative Bounds",
        "H15": "Cancellation Structure",
        "General": "General Theory",
        "Routes": "Alternative Routes"
    }

    generated = 0
    for paper in papers:
        paper_id = paper['id']

        # Extract enhanced concepts and tools
        concepts = extract_concepts_enhanced(
            paper['title'],
            paper.get('tags', []),
            paper.get('role_in_project', 'General'),
            paper['year']
        )

        tools = extract_tools_enhanced(
            paper.get('tags', []),
            paper['title']
        )

        # Build knowledge graph object
        kg = {
            'paper_id': paper_id,
            'title': paper['title'],
            'authors': [a['name'] for a in paper.get('authors', [])],
            'year': paper['year'],
            'phase': role_to_phase.get(paper.get('role_in_project', 'General'), 'General'),
            'key_concepts': concepts,
            'tools_used': tools,
            'related_papers': [],
            'statistics': {
                'relevance_score': paper.get('relevance_score', 0.5),
                'authors_count': len(paper.get('authors', [])),
            }
        }

        # Find related papers (same phase)
        phase = paper.get('role_in_project', 'General')
        related = [p['id'] for p in papers
                   if p.get('role_in_project') == phase and p['id'] != paper['id']][:5]
        kg['related_papers'] = related

        # Generate HTML
        html = generate_paper_knowledge_graph_html_improved(kg, paper_id)
        safe_id = paper_id.replace('/', '_')
        output_file = output_dir / f"kg_{safe_id}.html"
        output_file.write_text(html)

        generated += 1
        if generated % 5 == 0:
            print(f"  ✅ Generated {generated}/{len(papers)} pages")

    print(f"✅ Generated {generated} enhanced knowledge graph pages")
    print("=" * 70)
    print("\n🎉 All pages improved with:")
    print("  • Rich concept extraction (titles, tags, phase, year)")
    print("  • Tool extraction and categorization")
    print("  • Wide 'Extraction Details' section at top")
    print("  • Never-empty concept/tool/paper lists")
    print("  • Improved styling and readability")

if __name__ == "__main__":
    main()
