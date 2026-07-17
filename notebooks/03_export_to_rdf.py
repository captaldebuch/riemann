#!/usr/bin/env python3
"""
LOD / RDF Exporter for Mathematical Knowledge Graph
Converts the JSON corpus into RDF Triples using BIBFRAME, Dublin Core, FOAF, and SKOS.
Includes a stub for Identifier Alignment via Crossref/arXiv.
"""

import json
import urllib.request
import urllib.parse
from pathlib import Path
try:
    from rdflib import Graph, URIRef, Literal, Namespace, BNode
    from rdflib.namespace import RDF, RDFS, FOAF, DCTERMS, SKOS
except ImportError:
    print("Warning: rdflib not installed. Run `pip install rdflib` to generate triples.")
    Graph, URIRef, Literal, Namespace, BNode = None, None, None, None, None
    RDF, RDFS, FOAF, DCTERMS, SKOS = None, None, None, None, None

# Namespaces
MATHLIT = Namespace("https://captaldebuch.github.io/riemann/ontology#")
BIBO = Namespace("http://purl.org/ontology/bibo/")
CITO = Namespace("http://purl.org/spar/cito/")
WDT = Namespace("http://www.wikidata.org/prop/direct/")
WD = Namespace("http://www.wikidata.org/entity/")

def align_metadata(paper_data: dict) -> dict:
    """
    STUB: Identifier Alignment Pipeline
    In a full implementation, this would query the Crossref or arXiv API
    to validate titles, authors, and fetch DOI/arXiv URIs.
    It would also query the Wikidata SPARQL endpoint to find Author ORCID/VIAF/Wikidata URIs.
    """
    print(f"Aligning metadata for {paper_data.get('title')}...")
    
    # Example logic: if we have a DOI, query Crossref
    doi = paper_data.get('doi')
    if doi:
        # e.g., crossref_url = f"https://api.crossref.org/works/{doi}"
        pass 
        
    return paper_data

def export_kg_to_rdf(kg_json_path: str, output_ttl_path: str):
    if Graph is None:
        return
        
    with open(kg_json_path, 'r') as f:
        corpus = json.load(f)
        
    g = Graph()
    g.bind("mathlit", MATHLIT)
    g.bind("dcterms", DCTERMS)
    g.bind("foaf", FOAF)
    g.bind("bibo", BIBO)
    g.bind("cito", CITO)
    g.bind("skos", SKOS)
    g.bind("wd", WD)
    g.bind("wdt", WDT)

    # Note: corpus is assumed to be a dictionary matching MathematicalLiteratureDatabase
    # or just a list of MathematicalPaperKnowledgeGraph objects for this example.
    # Let's handle a single paper structure as defined in 02_knowledge_graph_parser.py
    
    if "id" in corpus and corpus["id"].startswith("paper:"):
        papers = [corpus]
    elif "paper_id" in corpus:
        papers = [corpus]
    else:
        papers = corpus.get("articles", [])
        
    for paper in papers:
        paper = align_metadata(paper)
        
        # Article Node
        paper_id_raw = paper.get('paper_id') or paper.get('id', '')
        arxiv_id = paper_id_raw.replace('arxiv:', '').replace('paper:', '')
        paper_uri = URIRef(paper.get('arxiv_uri') or f"https://arxiv.org/abs/{arxiv_id}")
        
        g.add((paper_uri, RDF.type, BIBO.Article))
        g.add((paper_uri, DCTERMS.title, Literal(paper.get('title'))))
        
        if paper.get('year'):
            g.add((paper_uri, DCTERMS.issued, Literal(str(paper.get('year')))))
            
        if paper.get('doi_uri'):
            g.add((paper_uri, BIBO.doi, URIRef(paper['doi_uri'])))

        # Authors
        for author in paper.get('authors', []):
            if isinstance(author, dict):
                name = author.get('name')
                author_uri_str = author.get('wikidata_uri') or author.get('orcid_uri') or author.get('viaf_uri')
                if author_uri_str:
                    author_uri = URIRef(author_uri_str)
                else:
                    # Fallback to a BNode or a generated local URI
                    safe_name = urllib.parse.quote(name.replace(" ", "_"))
                    author_uri = URIRef(f"https://captaldebuch.github.io/riemann/author/{safe_name}")
                
                g.add((author_uri, RDF.type, FOAF.Person))
                g.add((author_uri, FOAF.name, Literal(name)))
                g.add((paper_uri, DCTERMS.creator, author_uri))
                
                if author.get('orcid_uri'):
                    g.add((author_uri, DCTERMS.identifier, URIRef(author['orcid_uri'])))

        # Mathematical Objects (Theorems, Definitions)
        objects = paper.get('objects', {})
        if isinstance(objects, dict):
            objects_list = objects.values()
        else:
            objects_list = objects
            
        for obj in objects_list:
            obj_id = obj.get('id')
            obj_uri = URIRef(MATHLIT[obj_id])
            
            g.add((obj_uri, RDF.type, SKOS.Concept))
            g.add((obj_uri, SKOS.prefLabel, Literal(obj.get('name'))))
            g.add((obj_uri, SKOS.definition, Literal(obj.get('statement'))))
            g.add((paper_uri, DCTERMS.hasPart, obj_uri))
            
            if obj.get('wikidata_uri'):
                g.add((obj_uri, RDFS.seeAlso, URIRef(obj['wikidata_uri'])))

    # Serialize
    g.serialize(destination=output_ttl_path, format="turtle")
    
    # Also save JSON-LD
    jsonld_path = str(output_ttl_path).replace('.ttl', '.jsonld')
    g.serialize(destination=jsonld_path, format="json-ld")
    
    print(f"Exported RDF graph to {output_ttl_path} and {jsonld_path}")
    print(f"Total Triples: {len(g)}")

if __name__ == "__main__":
    import sys
    if len(sys.argv) > 2:
        export_kg_to_rdf(sys.argv[1], sys.argv[2])
    else:
        print("Usage: 03_export_to_rdf.py <input.json> <output.ttl>")
