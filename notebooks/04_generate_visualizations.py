#!/usr/bin/env python3
"""
Generate Additional Data Visualizations
- Schema Coverage Heatmap
- Formalization Potential Scatter Plot
- Theorem Network Graph
"""

import json
from pathlib import Path
import pandas as pd
import plotly.express as px
import matplotlib.pyplot as plt
import seaborn as sns
import networkx as nx
from pyvis.network import Network

DB_PATH = Path("rh_corpus_database.json")
VIZ_OUTPUT = Path("doc/html/visualizations")
VIZ_OUTPUT.mkdir(exist_ok=True, parents=True)

def load_db():
    if not DB_PATH.exists():
        print(f"Error: {DB_PATH} not found.")
        return None
    with open(DB_PATH, 'r') as f:
        return json.load(f)

def generate_schema_coverage(db):
    print("Generating Schema Coverage Heatmap...")
    articles = db.get("articles", [])
    insights = db.get("insights", [])
    intuitions = db.get("intuitions", [])
    formalizations = db.get("formalization", [])
    connections = db.get("connections", [])

    coverage_data = []
    
    for article in articles:
        aid = article.get("id")
        
        # Check insights
        insight = next((i for i in insights if i.get("article_id") == aid), None)
        has_insights = 1 if insight and insight.get("main_theorem") else 0
        
        # Check intuitions
        intuition = next((i for i in intuitions if i.get("article_id") == aid), None)
        has_intuitions = 1 if intuition and (intuition.get("author_intuitions") or intuition.get("extracted_intuitions")) else 0
        
        # Check formalization
        form = next((f for f in formalizations if f.get("article_id") == aid), None)
        has_formalization = 1 if form and form.get("formalizable_theorems") else 0
        
        # Check connections
        has_connections = 1 if any(c.get("source_id") == aid or c.get("target_id") == aid for c in connections) else 0

        coverage_data.append({
            "Article": article.get("title")[:20] + "...",
            "Metadata": 1,
            "Insights": has_insights,
            "Intuitions": has_intuitions,
            "Formalization": has_formalization,
            "Connections": has_connections
        })
        
    df = pd.DataFrame(coverage_data)
    if df.empty:
        print("No data for schema coverage.")
        return
        
    df.set_index("Article", inplace=True)
    
    plt.figure(figsize=(10, len(df)*0.5 + 2))
    sns.heatmap(df, annot=True, cmap="YlGnBu", cbar=False, linewidths=.5)
    plt.title("Schema Coverage by Article")
    plt.tight_layout()
    plt.savefig(VIZ_OUTPUT / "schema_coverage.png", dpi=150)
    plt.close()
    print("Saved schema_coverage.png")

def generate_formalization_scatter(db):
    print("Generating Formalization Scatter Plot...")
    articles = {a["id"]: a for a in db.get("articles", [])}
    formalizations = db.get("formalization", [])
    
    scatter_data = []
    for form in formalizations:
        aid = form.get("article_id")
        article = articles.get(aid)
        if not article: continue
            
        readiness = form.get("overall_readiness", 0)
        deps_count = len(form.get("mathlib_dependencies", []))
        estimated_weeks = form.get("estimated_weeks", 0)
        
        scatter_data.append({
            "Title": article.get("title"),
            "Role": article.get("role_in_project", "Unknown"),
            "Readiness Score": readiness,
            "Mathlib Dependencies": deps_count,
            "Estimated Weeks": estimated_weeks
        })
        
    df = pd.DataFrame(scatter_data)
    if df.empty:
        print("No data for formalization scatter.")
        return
        
    fig = px.scatter(
        df,
        x="Readiness Score", 
        y="Mathlib Dependencies",
        size="Estimated Weeks" if "Estimated Weeks" in df and df["Estimated Weeks"].sum() > 0 else None,
        color="Role",
        hover_name="Title",
        title="Formalization Readiness vs. Missing Dependencies",
        labels={"Readiness Score": "Lean 4 Readiness (0 to 1)", "Mathlib Dependencies": "Number of Mathlib Gaps"}
    )
    fig.write_html(str(VIZ_OUTPUT / "formalization_scatter.html"))
    print("Saved formalization_scatter.html")

def generate_theorem_network(db):
    print("Generating Theorem Network...")
    
    G = nx.DiGraph()
    insights = db.get("insights", [])
    
    # Simple logic: extract all theorems and techniques
    for insight in insights:
        aid = insight.get("article_id")
        main_th = insight.get("main_theorem")
        
        if main_th:
            label = main_th.get("label", "Theorem")
            G.add_node(label, group="theorem", title=main_th.get("statement", ""), color="#ef4444")
            
            for tech in insight.get("key_techniques", []):
                t_name = tech.get("name")
                G.add_node(t_name, group="technique", title=tech.get("description", ""), color="#3b82f6")
                G.add_edge(label, t_name, title="Uses Technique")
                
            for obj in insight.get("mathematical_objects", []):
                o_name = obj.get("name")
                G.add_node(o_name, group="object", title=obj.get("definition", ""), color="#10b981")
                G.add_edge(label, o_name, title="Relies On Object")

    if G.number_of_nodes() == 0:
        print("No theorem data found.")
        return

    net = Network(height="600px", width="100%", directed=True)
    net.from_nx(G)
    net.show_buttons(filter_=['physics'])
    net.save_graph(str(VIZ_OUTPUT / "theorem_network.html"))
    print("Saved theorem_network.html")

if __name__ == "__main__":
    db = load_db()
    if db:
        generate_schema_coverage(db)
        generate_formalization_scatter(db)
        generate_theorem_network(db)
        print("✅ Visualizations generated successfully.")
