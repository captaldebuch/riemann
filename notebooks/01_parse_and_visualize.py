#!/usr/bin/env python
# coding: utf-8

# # Mathematical Literature Database: Parse & Visualize
# ## RH Corpus → Structured Knowledge → Interactive Visualizations
# 
# This notebook:
# 1. Parses papers using LLM + structured extraction
# 2. Builds the mathematical literature database
# 3. Generates four interactive visualizations
# 4. Exports for website integration

# ## Setup: Install Dependencies

# In[ ]:


get_ipython().system('pip install --quiet instructor pydantic networkx pyvis altair umap-learn scikit-learn plotly marker-pdf')
print("✅ Dependencies installed")


# ## 1. Load Schema & Setup

# In[ ]:


import json
from typing import List, Optional, Dict
from pydantic import BaseModel, Field
from datetime import date, datetime
import pandas as pd
import networkx as nx
from pyvis.network import Network
import altair as alt
import plotly.express as px
import numpy as np
from pathlib import Path
import os

# Set up paths
PAPERS_DIR = Path("../papers")
DB_OUTPUT = Path("./rh_corpus_database.json")
VIZ_OUTPUT = Path("./visualizations")
VIZ_OUTPUT.mkdir(exist_ok=True)

print(f"Papers directory: {PAPERS_DIR}")
print(f"Database output: {DB_OUTPUT}")
print(f"Visualizations will be saved to: {VIZ_OUTPUT}")


# ## 2. Define Pydantic Schema (from SCHEMA_MATHLIT_DATABASE.md)

# In[ ]:


class Author(BaseModel):
    name: str
    affiliation: Optional[str] = None

class Theorem(BaseModel):
    label: str
    statement: str
    proof_sketch: Optional[str] = None
    assumptions: List[str] = []

class Technique(BaseModel):
    name: str
    description: str
    used_in: List[str] = []

class MathematicalObject(BaseModel):
    name: str
    category: str
    definition: str
    key_properties: List[str] = []

class KeyInsights(BaseModel):
    article_id: str
    main_theorem: Optional[Theorem] = None
    key_theorems: List[Theorem] = []
    key_techniques: List[Technique] = []
    mathematical_objects: List[MathematicalObject] = []
    main_contribution: str
    open_problems: List[str] = []

class Intuition(BaseModel):
    type: str
    description: str
    supports_theorem: Optional[str] = None
    confidence: float = 0.7

class MathematicalIntuitions(BaseModel):
    article_id: str
    author_intuitions: List[Intuition] = []
    extracted_intuitions: List[Intuition] = []

class LeanDependency(BaseModel):
    concept: str
    status: str
    mathlib_module: Optional[str] = None
    estimated_effort: Optional[str] = None

class FormalizationPotential(BaseModel):
    article_id: str
    overall_readiness: float
    formalizable_theorems: List[str] = []
    mathlib_dependencies: List[LeanDependency] = []
    estimated_weeks: Optional[float] = None

class Connection(BaseModel):
    source_id: str
    target_id: str
    relationship: str
    description: str
    strength: float = 0.5

class ArticleReference(BaseModel):
    id: str
    title: str
    authors: List[Author]
    year: int
    arxiv_id: Optional[str] = None
    role_in_project: str
    relevance_score: float
    tags: List[str] = []
    local_pdf_path: str

class MathematicalLiteratureDatabase(BaseModel):
    version: str = "1.0"
    generated_date: str
    articles: List[ArticleReference]
    insights: List[KeyInsights]
    intuitions: List[MathematicalIntuitions]
    formalization: List[FormalizationPotential]
    connections: List[Connection]

print("✅ Schema loaded")


# ## 3. Load Sample Data (or Parse from PDFs)
# 
# For now, we'll load from a JSON file or create sample data. In production, this would use Marker + Claude API.

# In[ ]:


# Sample database for demonstration
sample_database = {
    "version": "1.0",
    "generated_date": datetime.now().isoformat(),
    "articles": [
        {
            "id": "arxiv:1111.0931",
            "title": "Approximations to the Riemann Hypothesis",
            "authors": [
                {"name": "Bettin"},
                {"name": "Conrey"}
            ],
            "year": 2013,
            "arxiv_id": "1111.0931",
            "role_in_project": "H15",
            "relevance_score": 0.95,
            "tags": ["möbius", "period-functions", "cotangent-sums"],
            "local_pdf_path": "1111.0931.pdf"
        },
        {
            "id": "arxiv:1601.06839",
            "title": "Reciprocal Relations and *-Type Theorems",
            "authors": [
                {"name": "Auli"},
                {"name": "Bayad"},
                {"name": "Beck"}
            ],
            "year": 2017,
            "arxiv_id": "1601.06839",
            "role_in_project": "H15",
            "relevance_score": 0.85,
            "tags": ["reciprocity", "cotangent-sums"],
            "local_pdf_path": "1601.06839.pdf"
        },
        {
            "id": "arxiv:1501.02975",
            "title": "Mellin Transform Techniques in Analytic Number Theory",
            "authors": [{"name": "Various"}],
            "year": 2015,
            "arxiv_id": "1501.02975",
            "role_in_project": "H14",
            "relevance_score": 0.9,
            "tags": ["mellin", "contour-analysis"],
            "local_pdf_path": "1501.02975.pdf"
        }
    ],
    "insights": [
        {
            "article_id": "arxiv:1111.0931",
            "main_theorem": {
                "label": "Theorem 1.1",
                "statement": "Period functional equation for cotangent sums",
                "proof_sketch": "Fourier analysis on GL(2)"
            },
            "main_contribution": "Explicit relation between RH and cotangent-sum bounds"
        }
    ],
    "intuitions": [
        {
            "article_id": "arxiv:1111.0931",
            "author_intuitions": [
                {
                    "type": "analogy",
                    "description": "Period functions behave like quantum modular forms",
                    "confidence": 0.6
                }
            ]
        }
    ],
    "formalization": [
        {
            "article_id": "arxiv:1111.0931",
            "overall_readiness": 0.6,
            "formalizable_theorems": ["Theorem 1.1"],
            "mathlib_dependencies": [
                {
                    "concept": "period-functions",
                    "status": "custom-dependency",
                    "estimated_effort": "medium"
                }
            ],
            "estimated_weeks": 3.5
        }
    ],
    "connections": [
        {
            "source_id": "arxiv:1111.0931",
            "target_id": "arxiv:1601.06839",
            "relationship": "uses-result-from",
            "description": "Bettin-Conrey apply reciprocity machinery from Auli-Bayad-Beck",
            "strength": 0.8
        },
        {
            "source_id": "arxiv:1501.02975",
            "target_id": "arxiv:1111.0931",
            "relationship": "provides-technique",
            "description": "Mellin techniques used throughout Bettin-Conrey",
            "strength": 0.9
        }
    ]
}

db = MathematicalLiteratureDatabase(**sample_database)
print(f"✅ Loaded database with {len(db.articles)} articles")
print(f"   {len(db.connections)} connections")


# ## 4. VIZ 1: Interactive Citation Network (Pyvis)

# In[ ]:


# Build NetworkX graph
G = nx.DiGraph()

# Add nodes (papers)
role_colors = {
    "H13": "#10b981",  # green
    "H14": "#3b82f6",  # blue
    "H15": "#ef4444",  # red
    "Phase_NB": "#f59e0b",  # amber
    "General": "#6b7280"  # gray
}

article_map = {a.id: a for a in db.articles}
in_degree = {conn.target_id: 0 for conn in db.connections}
for conn in db.connections:
    in_degree[conn.target_id] = in_degree.get(conn.target_id, 0) + 1

for article in db.articles:
    color = role_colors.get(article.role_in_project, "#6b7280")
    G.add_node(
        article.id,
        label=f"{article.authors[0].name} ({article.year})",
        title=f"{article.title}\nRelevance: {article.relevance_score:.1%}\nRole: {article.role_in_project}",
        color=color,
        size=10 + in_degree.get(article.id, 0) * 5
    )

# Add edges (connections)
for conn in db.connections:
    G.add_edge(
        conn.source_id,
        conn.target_id,
        title=f"{conn.relationship}\n{conn.description}",
        weight=conn.strength
    )

# Create Pyvis network
net = Network(
    directed=True,
    height="750px",
    width="100%",
    layout="force"
)
net.from_nx(G)
net.show_buttons(filter_=['physics'])
net.show(str(VIZ_OUTPUT / "citation_network.html"))

print(f"✅ Citation network saved to {VIZ_OUTPUT / 'citation_network.html'}")


# ## 5. VIZ 2: Lean Formalization Dependency (Graphviz)

# In[ ]:


from graphviz import Digraph

# Create dependency graph for most-formalized paper
target_article = db.articles[0]  # Bettin-Conrey
target_form = db.formalization[0]

dot = Digraph(comment='Lean Dependency DAG', format='svg')
dot.attr(rankdir='TB', size='10,8')
dot.attr('node', shape='box', style='rounded,filled', fillcolor='#f0f9ff')

# Root: main theorem
if target_form.main_theorem:
    dot.node('root', f"{target_form.main_theorem}\n(Main)", fillcolor='#10b981', fontcolor='white')
else:
    dot.node('root', f"{target_article.title}\n(Main Result)", fillcolor='#10b981', fontcolor='white')

# Dependencies
for i, dep in enumerate(target_form.mathlib_dependencies):
    status_color = '#d1fae5' if dep.status == 'available-in-mathlib' else '#fee2e2'
    dot.node(
        f'dep_{i}',
        f"{dep.concept}\n({dep.status})",
        fillcolor=status_color
    )
    dot.edge('root', f'dep_{i}', label=dep.estimated_effort or '')

# Base: Mathlib
dot.node('base', 'Mathlib / Axioms', shape='ellipse', fillcolor='#e0e7ff')
for i in range(len(target_form.mathlib_dependencies)):
    dot.edge(f'dep_{i}', 'base')

svg_path = str(VIZ_OUTPUT / 'lean_dependency_dag.svg')
dot.render(svg_path.replace('.svg', ''), quiet=True)

print(f"✅ Lean dependency DAG saved to {svg_path}")


# ## 6. VIZ 3: Chronological Domain Timeline (Altair)

# In[ ]:


# Create timeline data
timeline_data = []
for article in db.articles:
    form = next((f for f in db.formalization if f.article_id == article.id), None)
    timeline_data.append({
        'Year': article.year,
        'Title': article.title[:40] + '...' if len(article.title) > 40 else article.title,
        'Authors': ', '.join([a.name for a in article.authors[:2]]),
        'Role': article.role_in_project,
        'Lean Readiness': form.overall_readiness if form else 0,
        'ID': article.id,
        'Full Title': article.title
    })

timeline_df = pd.DataFrame(timeline_data)

# Create Altair chart
chart = alt.Chart(timeline_df).mark_circle(size=200).encode(
    x='Year:Q',
    y='Role:N',
    color='Lean Readiness:Q',
    tooltip=['Full Title:N', 'Authors:N', 'Year:Q', 'Lean Readiness:Q'],
    size=alt.Size('Lean Readiness:Q', scale=alt.Scale(range=[50, 300]))
).interactive().properties(
    width=900,
    height=400,
    title='Mathematical Literature Timeline: Era & Domain vs. Lean Formalization Readiness'
)

chart.save(str(VIZ_OUTPUT / 'timeline_domain.html'))
print(f"✅ Timeline saved to {VIZ_OUTPUT / 'timeline_domain.html'}")


# ## 7. VIZ 4: Semantic Concept Clusters (t-SNE Embedding)

# In[ ]:


from sklearn.manifold import TSNE
from sklearn.feature_extraction.text import TfidfVectorizer

# Extract intuitions and insights as "concept documents"
concept_texts = []
concept_labels = []
concept_articles = []

for intuition in db.intuitions:
    text = " ".join([
        i.description for i in intuition.author_intuitions + intuition.extracted_intuitions
    ])
    if text.strip():
        concept_texts.append(text)
        concept_articles.append(intuition.article_id)
        concept_labels.append(intuition.article_id)

# Vectorize
if len(concept_texts) > 1:
    vectorizer = TfidfVectorizer(max_features=50)
    X = vectorizer.fit_transform(concept_texts).toarray()

    # Apply t-SNE
    tsne = TSNE(n_components=2, random_state=42, perplexity=min(5, len(X)-1))
    X_embedded = tsne.fit_transform(X)

    # Create dataframe
    concept_df = pd.DataFrame({
        'x': X_embedded[:, 0],
        'y': X_embedded[:, 1],
        'Paper': [article_map.get(aid).title for aid in concept_articles],
        'ID': concept_articles,
        'Role': [article_map.get(aid).role_in_project for aid in concept_articles]
    })

    # Plotly scatter
    fig = px.scatter(
        concept_df,
        x='x', y='y',
        color='Role',
        hover_name='Paper',
        title='Semantic Concept Clustering (t-SNE): Papers by Intuition Similarity',
        height=600
    )
    fig.write_html(str(VIZ_OUTPUT / 'semantic_clusters.html'))
    print(f"✅ Semantic clusters saved to {VIZ_OUTPUT / 'semantic_clusters.html'}")
else:
    print("⚠️  Not enough intuitions for semantic clustering")


# ## 8. Export Database as JSON

# In[ ]:


# Save database
with open(DB_OUTPUT, 'w') as f:
    json.dump(db.model_dump(), f, indent=2, default=str)

print(f"✅ Database saved to {DB_OUTPUT}")
print(f"\n📊 VISUALIZATIONS GENERATED:")
print(f"   1. Citation Network: {VIZ_OUTPUT / 'citation_network.html'}")
print(f"   2. Lean Dependency DAG: {VIZ_OUTPUT / 'lean_dependency_dag.svg'}")
print(f"   3. Timeline Domain Chart: {VIZ_OUTPUT / 'timeline_domain.html'}")
print(f"   4. Semantic Clusters: {VIZ_OUTPUT / 'semantic_clusters.html'}")
print(f"\n📁 Copy these to /doc/html/ for website integration.")

