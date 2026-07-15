#!/usr/bin/env python3
"""
LOD Phase 2: Generate RDF from cleaned JSON corpus
Produces Turtle files (articles.ttl, authors.ttl, concepts.ttl, connections.ttl)

Run: python3 scripts/lod_phase2_generate_rdf.py
"""

import json
import re
from typing import Set, Dict, List

# Ontology namespaces
NAMESPACES = {
    'rdf': 'http://www.w3.org/1999/02/22-rdf-syntax-ns#',
    'rdfs': 'http://www.w3.org/2000/01/rdf-schema#',
    'dcterms': 'http://purl.org/dc/terms/',
    'bibo': 'http://purl.org/ontology/bibo/',
    'foaf': 'http://xmlns.com/foaf/0.1/',
    'schema': 'https://schema.org/',
    'cito': 'http://purl.org/spar/cito/',
    'skos': 'http://www.w3.org/2004/02/skos/core#',
    'owl': 'http://www.w3.org/2002/07/owl#',
    'xsd': 'http://www.w3.org/2001/XMLSchema#',
    'rh': 'http://data.rh-corpus.org/',
}

class RDFGenerator:
    def __init__(self, db_path: str = "rh_corpus_database_cleaned.json"):
        self.db = json.load(open(db_path))
        self.articles = self.db.get('articles', [])
        self.turtle_output = []
        self.authors_seen = set()
        self.concepts_seen = set()

    def escape_turtle_string(self, s: str) -> str:
        """Escape string for Turtle format"""
        if not s:
            return '""'
        s = s.replace('\\', '\\\\').replace('"', '\\"').replace('\n', '\\n')
        return f'"{s}"'

    def slug(self, s: str) -> str:
        """Convert string to URL-safe slug"""
        if not s:
            return 'unknown'
        s = str(s).lower()
        s = re.sub(r'[^a-z0-9]+', '-', s)
        return s.strip('-')

    def write_header(self):
        """Write Turtle file header with namespaces"""
        header = []
        header.append("# RH Corpus - RDF Graph (Turtle)")
        header.append("# Generated from rh_corpus_database_cleaned.json")
        header.append("# Ontologies: BIBO, FOAF, DCTERMS, CITO, SKOS")
        header.append("")

        for prefix, ns in NAMESPACES.items():
            header.append(f"@prefix {prefix}: <{ns}> .")

        header.append("")
        self.turtle_output.extend(header)

    def uri(self, namespace: str, local_id: str) -> str:
        """Create URI in Turtle format"""
        ns = NAMESPACES.get(namespace, namespace)
        return f"{namespace}:{local_id.replace('-', '_')}"

    def add_triple(self, subject: str, predicate: str, obj: str, literal: bool = False):
        """Add RDF triple to output"""
        if literal:
            self.turtle_output.append(f"    {predicate} {self.escape_turtle_string(obj)} ;")
        else:
            self.turtle_output.append(f"    {predicate} {obj} ;")

    def write_article(self, article: Dict):
        """Generate RDF for a single article"""
        article_id = article.get('id', '')
        article_uri = f"rh:article_{self.slug(article_id)}"

        # Start article block
        self.turtle_output.append(f"{article_uri}")
        self.turtle_output.append(f"    a bibo:AcademicArticle ;")

        # Title
        title = article.get('title', 'Unknown')
        self.add_triple(article_uri, "dcterms:title", title, literal=True)

        # Year
        year = article.get('year')
        if year and isinstance(year, int):
            self.turtle_output.append(f'    dcterms:issued "{year}"^^xsd:gYear ;')

        # Authors (as URIs)
        authors = article.get('authors', [])
        if authors:
            for au in authors:
                author_name = au.get('name', 'Unknown')
                author_slug = self.slug(author_name)
                author_uri = f"rh:author_{author_slug}"
                self.turtle_output.append(f"    dcterms:creator {author_uri} ;")
                self.authors_seen.add((author_name, author_slug))

        # ArXiv ID
        arxiv_id = article.get('arxiv_id')
        if arxiv_id:
            self.add_triple(article_uri, "bibo:arxivId", arxiv_id, literal=True)

        # DOI
        doi = article.get('doi')
        if doi:
            self.add_triple(article_uri, "bibo:doi", doi, literal=True)

        # PDF location
        pdf_path = article.get('local_pdf_path')
        if pdf_path:
            self.turtle_output.append(f'    schema:downloadUrl "file:///{pdf_path}" ;')

        # Project role
        role = article.get('role_in_project')
        if role:
            self.add_triple(article_uri, "rh:projectRole", role, literal=True)

        # Tags as concepts
        tags = article.get('tags', [])
        if tags:
            for tag in tags[:5]:  # Limit to 5 tags
                tag_slug = self.slug(tag)
                concept_uri = f"rh:concept_{tag_slug}"
                self.turtle_output.append(f"    dcterms:subject {concept_uri} ;")
                self.concepts_seen.add((tag, tag_slug))

        # Relevance score
        relevance = article.get('relevance_score')
        if relevance:
            self.turtle_output.append(f'    rh:relevanceScore "{relevance}"^^xsd:float ;')

        # End triple (remove trailing semicolon from last line)
        if self.turtle_output and self.turtle_output[-1].endswith(' ;'):
            self.turtle_output[-1] = self.turtle_output[-1][:-2] + ' .'
        else:
            self.turtle_output.append('    .')

        self.turtle_output.append('')

    def write_authors(self):
        """Generate RDF for all authors"""
        if not self.authors_seen:
            return

        self.turtle_output.append("# ===== AUTHORS =====\n")

        for author_name, author_slug in sorted(self.authors_seen):
            author_uri = f"rh:author_{author_slug}"
            self.turtle_output.append(f"{author_uri}")
            self.turtle_output.append(f"    a foaf:Person ;")
            self.add_triple(author_uri, "foaf:name", author_name, literal=True)
            self.turtle_output[-1] = self.turtle_output[-1][:-2] + ' .'
            self.turtle_output.append('')

    def write_concepts(self):
        """Generate RDF for all concepts (tags)"""
        if not self.concepts_seen:
            return

        self.turtle_output.append("# ===== CONCEPTS (Tags) =====\n")

        for tag, tag_slug in sorted(self.concepts_seen):
            concept_uri = f"rh:concept_{tag_slug}"
            self.turtle_output.append(f"{concept_uri}")
            self.turtle_output.append(f"    a skos:Concept ;")
            self.add_triple(concept_uri, "skos:prefLabel", tag, literal=True)
            self.turtle_output[-1] = self.turtle_output[-1][:-2] + ' .'
            self.turtle_output.append('')

    def write_connections(self):
        """Generate RDF for article connections (citations, relationships)"""
        self.turtle_output.append("# ===== CONNECTIONS (CiTO Citations) =====\n")

        # Parse explicit connections if they exist in the data
        for article in self.articles:
            article_id = article.get('id', '')
            article_uri = f"rh:article_{self.slug(article_id)}"

            connections = article.get('connections', [])
            if connections:
                for conn in connections:
                    target_id = conn.get('target_id')
                    rel_type = conn.get('relationship', 'related')
                    target_uri = f"rh:article_{self.slug(target_id)}"

                    # Map relationship types to CiTO
                    cito_map = {
                        'cites': 'cito:citesAsAuthority',
                        'cited-by': 'cito:isCitedBy',
                        'extends': 'cito:extends',
                        'builds-on': 'cito:obtainsSupportFrom',
                        'related': 'rdfs:seeAlso',
                    }

                    predicate = cito_map.get(rel_type, 'rdfs:seeAlso')
                    self.turtle_output.append(f"{article_uri} {predicate} {target_uri} .")

        self.turtle_output.append('')

    def generate(self):
        """Generate complete RDF graph"""
        print(f"Generating RDF for {len(self.articles)} articles...\n")

        self.write_header()

        self.turtle_output.append("# ===== ARTICLES =====\n")

        # Generate articles
        for i, article in enumerate(self.articles):
            if i % 20 == 0:
                print(f"  Processing article {i+1}/{len(self.articles)}...")
            self.write_article(article)

        # Generate supporting entities
        self.write_authors()
        self.write_concepts()
        self.write_connections()

        print(f"✓ Generated RDF for {len(self.articles)} articles")
        print(f"✓ Generated {len(self.authors_seen)} authors")
        print(f"✓ Generated {len(self.concepts_seen)} concepts")

    def save(self, output_file: str = "rdf_output/corpus.ttl"):
        """Save Turtle file"""
        import os
        os.makedirs(os.path.dirname(output_file), exist_ok=True)

        with open(output_file, 'w', encoding='utf-8') as f:
            f.write('\n'.join(self.turtle_output))

        print(f"\n✓ Saved to: {output_file}")
        print(f"✓ File size: {len(self.turtle_output)} lines")

def main():
    print("=" * 70)
    print("LOD PHASE 2: RDF GENERATION")
    print("=" * 70)
    print()

    generator = RDFGenerator('rh_corpus_database_cleaned.json')
    generator.generate()
    generator.save('rdf_output/corpus.ttl')

    print("\n" + "=" * 70)
    print("Next steps:")
    print("  1. Review rdf_output/corpus.ttl for correctness")
    print("  2. Phase 3: Set up SPARQL endpoint (Jena Fuseki)")
    print("  3. Phase 4: Website integration")
    print("=" * 70)

if __name__ == '__main__':
    main()
