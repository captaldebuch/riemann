#!/usr/bin/env python3
"""
Integrate knowledge graph links into the website
"""

import json
import re
from pathlib import Path

def get_knowledge_graphs():
    """Load knowledge graph data"""
    kg_json = Path("/Users/xavierfresquet/Documents/Musicologie/CAPTAL-LAB/4-MISC/math/riemann/doc/html/knowledge_graphs.json")
    if kg_json.exists():
        with open(kg_json) as f:
            return json.load(f).get('knowledge_graphs', {})
    return {}

def sanitize_filename(paper_id):
    """Sanitize paper ID for use as filename"""
    return paper_id.replace('/', '_')

def update_all_navigations(html_dir):
    """Update navigation on all HTML files to include knowledge graph explorer"""

    nav_old = '''  <nav>
    <ul>
      <li><a href="index.html">Home</a></li>
      <li><a href="intro.html">Vision & Method</a></li>
      <li><a href="corpus.html">📚 Complete Corpus</a></li>
      <li><a href="mathematicians.html">👥 Mathematicians</a></li>
      <li><a href="visualizations.html">📊 Visualizations</a></li>
      <li><a href="about.html">About</a></li>
    </ul>
  </nav>'''

    nav_new = '''  <nav>
    <ul>
      <li><a href="index.html">Home</a></li>
      <li><a href="intro.html">Vision & Method</a></li>
      <li><a href="corpus.html">📚 Complete Corpus</a></li>
      <li><a href="mathematicians.html">👥 Mathematicians</a></li>
      <li><a href="visualizations.html">📊 Visualizations</a></li>
      <li><a href="knowledge-explorer.html">🔗 Knowledge Graph</a></li>
      <li><a href="about.html">About</a></li>
    </ul>
  </nav>'''

    html_files = list(html_dir.glob("*.html"))
    for html_file in html_files:
        # Skip knowledge graph files themselves
        if html_file.name.startswith("kg_") or html_file.name == "knowledge-explorer.html":
            continue

        content = html_file.read_text()
        if nav_old in content:
            # Update all nav links to mark active based on filename
            page_name = html_file.stem

            # Replace static nav with dynamic one
            updated = content.replace(nav_old, nav_new)

            # Mark current page as active
            active_marker = f'<a href="{html_file.name}" class="active">'
            updated = re.sub(
                r'<li><a href="' + re.escape(html_file.name) + r'">',
                f'<li><a href="{html_file.name}" class="active">',
                updated
            )

            html_file.write_text(updated)
            print(f"✅ Updated navigation: {html_file.name}")

def add_kg_links_to_corpus(html_dir, kgs):
    """Add knowledge graph links to corpus.html"""

    corpus_file = html_dir / "corpus.html"
    if not corpus_file.exists():
        print("⚠️  corpus.html not found, skipping")
        return

    # Create a mapping of paper IDs to knowledge graphs
    kg_map = {pid: kg for pid, kg in kgs.items()}

    content = corpus_file.read_text()

    # Find the table body and add KG links
    # This is a bit fragile, so we'll be careful

    # Check if we already have KG integration
    if 'knowledge-explorer.html' in content:
        print("✅ corpus.html already has knowledge graph links")
        return

    # Add a section about knowledge graphs
    kg_intro = '''
    <article>
      <h2>🔗 Knowledge Graphs</h2>
      <p>Each paper in our corpus has been analyzed and represented as a structured knowledge graph, extracting:</p>
      <ul>
        <li><strong>Key Concepts:</strong> Mathematical themes and techniques</li>
        <li><strong>Mathematical Tools:</strong> Fourier analysis, Mellin transforms, contour integration, etc.</li>
        <li><strong>Related Papers:</strong> Other papers in the same phase</li>
        <li><strong>Statistics:</strong> Relevance score, author count, and connections</li>
      </ul>
      <p><a href="knowledge-explorer.html"><strong>📊 Explore the Knowledge Graph →</strong></a></p>
    </article>
'''

    # Insert before the closing </main> tag
    if '</main>' in content:
        content = content.replace('</main>', kg_intro + '\n  </main>')
        corpus_file.write_text(content)
        print("✅ Added knowledge graph section to corpus.html")

def main():
    html_dir = Path("/Users/xavierfresquet/Documents/Musicologie/CAPTAL-LAB/4-MISC/math/riemann/doc/html")
    kgs = get_knowledge_graphs()

    print("🔗 Integrating Knowledge Graphs into Website")
    print("=" * 70)

    # Update navigations
    print("\n📝 Updating navigation on all pages...")
    update_all_navigations(html_dir)

    # Add KG intro to corpus
    print("\n📚 Enhancing corpus.html...")
    add_kg_links_to_corpus(html_dir, kgs)

    print("\n" + "=" * 70)
    print("✅ Integration complete!")
    print(f"📍 Location: {html_dir}")
    print(f"🌐 Visit: doc/html/knowledge-explorer.html")
    print(f"📊 Individual papers: doc/html/kg_<paper-id>.html")

if __name__ == "__main__":
    main()
