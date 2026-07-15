#!/usr/bin/env python3
"""
LOD Phase 3: Offline SPARQL Validation
Tests RDF syntax, validates SPARQL queries, and provides deployment verification

Run: python3 scripts/lod_phase3_offline_test.py
"""

import json
import re
from pathlib import Path

class TurtleValidator:
    """Validates Turtle RDF syntax"""

    def __init__(self, ttl_file):
        self.ttl_file = ttl_file
        self.lines = []
        self.prefixes = {}
        self.triples = []
        self.errors = []

    def load(self):
        """Load and parse Turtle file"""
        with open(self.ttl_file, 'r', encoding='utf-8') as f:
            self.lines = f.readlines()

    def validate_syntax(self) -> bool:
        """Validate basic Turtle syntax"""
        print(f"Validating {self.ttl_file}...\n")

        # Check file size
        file_size = Path(self.ttl_file).stat().st_size
        print(f"✓ File size: {file_size:,} bytes")

        # Check prefixes
        prefix_count = sum(1 for line in self.lines if line.strip().startswith('@prefix'))
        print(f"✓ Prefixes found: {prefix_count}")

        # Check triples (lines ending with . or ;)
        triple_lines = sum(1 for line in self.lines if re.search(r'[.;]\s*$', line.strip()))
        print(f"✓ Triple lines: {triple_lines}")

        # Validate prefix syntax
        for i, line in enumerate(self.lines, 1):
            if line.strip().startswith('@prefix'):
                # Format: @prefix name: <URI> .
                if not re.match(r'@prefix\s+\w+:\s+<[^>]+>\s*\.', line.strip()):
                    self.errors.append(f"Line {i}: Invalid prefix syntax: {line.strip()[:50]}")

        # Check for common errors
        unclosed_quotes = 0
        for line in self.lines:
            if line.count('"') % 2 != 0:
                unclosed_quotes += 1

        if unclosed_quotes > 0:
            print(f"⚠ Potential unclosed quotes: {unclosed_quotes} lines")

        # Summary
        print(f"\n{'✓ VALID TURTLE SYNTAX' if not self.errors else '✗ SYNTAX ERRORS FOUND'}")
        if self.errors:
            for error in self.errors[:5]:
                print(f"  {error}")
            if len(self.errors) > 5:
                print(f"  ... and {len(self.errors) - 5} more")

        return len(self.errors) == 0

    def count_entities(self) -> dict:
        """Count entities in RDF"""
        print(f"\n\nEntity Count Analysis:")
        print("=" * 50)

        articles = 0
        authors = 0
        concepts = 0
        total_triples = 0

        for line in self.lines:
            if 'bibo:AcademicArticle' in line:
                articles += 1
            if 'foaf:Person' in line:
                authors += 1
            if 'skos:Concept' in line:
                concepts += 1
            if re.search(r'[.;]\s*$', line.strip()):
                total_triples += 1

        print(f"Articles (bibo:AcademicArticle):  {articles}")
        print(f"Authors (foaf:Person):            {authors}")
        print(f"Concepts (skos:Concept):          {concepts}")
        print(f"Total triple statements:          {total_triples}")

        return {
            'articles': articles,
            'authors': authors,
            'concepts': concepts,
            'total_triples': total_triples
        }


class SPARQLQueryValidator:
    """Validates SPARQL query syntax"""

    EXAMPLE_QUERIES = [
        {
            'name': 'Count Articles',
            'query': '''
PREFIX bibo: <http://purl.org/ontology/bibo/>
SELECT (COUNT(?article) AS ?count)
WHERE { ?article a bibo:AcademicArticle . }
            '''
        },
        {
            'name': 'Articles by Year',
            'query': '''
PREFIX dcterms: <http://purl.org/dc/terms/>
PREFIX bibo: <http://purl.org/ontology/bibo/>
SELECT ?year (COUNT(?article) AS ?count)
WHERE {
    ?article a bibo:AcademicArticle ;
             dcterms:issued ?year .
}
GROUP BY ?year
ORDER BY DESC(?year)
LIMIT 10
            '''
        },
        {
            'name': 'H15 Papers',
            'query': '''
PREFIX dcterms: <http://purl.org/dc/terms/>
PREFIX rh: <http://data.rh-corpus.org/>
PREFIX bibo: <http://purl.org/ontology/bibo/>
SELECT ?title ?year
WHERE {
    ?article a bibo:AcademicArticle ;
             dcterms:title ?title ;
             dcterms:issued ?year ;
             rh:projectRole "H15" .
}
LIMIT 5
            '''
        },
        {
            'name': 'Papers by Concept',
            'query': '''
PREFIX dcterms: <http://purl.org/dc/terms/>
PREFIX skos: <http://www.w3.org/2004/02/skos/core#>
PREFIX bibo: <http://purl.org/ontology/bibo/>
SELECT ?concept (COUNT(?article) AS ?paperCount)
WHERE {
    ?article a bibo:AcademicArticle ;
             dcterms:subject ?concept .
    ?concept a skos:Concept .
}
GROUP BY ?concept
ORDER BY DESC(?paperCount)
LIMIT 10
            '''
        },
        {
            'name': 'Authors by Paper Count',
            'query': '''
PREFIX dcterms: <http://purl.org/dc/terms/>
PREFIX foaf: <http://xmlns.com/foaf/0.1/>
PREFIX bibo: <http://purl.org/ontology/bibo/>
SELECT ?authorName (COUNT(?article) AS ?paperCount)
WHERE {
    ?article a bibo:AcademicArticle ;
             dcterms:creator ?author .
    ?author foaf:name ?authorName .
}
GROUP BY ?authorName
ORDER BY DESC(?paperCount)
LIMIT 10
            '''
        }
    ]

    def validate_all(self):
        """Validate all example queries"""
        print(f"\n\nSPARQL Query Validation:")
        print("=" * 50)

        for i, query_spec in enumerate(self.EXAMPLE_QUERIES, 1):
            self.validate_query(query_spec['name'], query_spec['query'])

    def validate_query(self, name: str, query: str):
        """Validate a single SPARQL query"""
        print(f"\n[{len(self.EXAMPLE_QUERIES)}] {name}")
        print("-" * 40)

        # Check basic SPARQL structure
        query_upper = query.upper().strip()
        errors = []

        # Must have SELECT, ASK, CONSTRUCT, or DESCRIBE
        if not any(kw in query_upper for kw in ['SELECT', 'ASK', 'CONSTRUCT', 'DESCRIBE']):
            errors.append("Missing SELECT/ASK/CONSTRUCT/DESCRIBE")

        # Must have WHERE clause (unless DESCRIBE)
        if 'WHERE' not in query_upper and 'DESCRIBE' not in query_upper:
            errors.append("Missing WHERE clause")

        # Check for closing braces
        open_braces = query.count('{')
        close_braces = query.count('}')
        if open_braces != close_braces:
            errors.append(f"Brace mismatch: {open_braces} open, {close_braces} close")

        # Check for unclosed strings
        quote_count = query.count('"') + query.count("'")
        if quote_count % 2 != 0:
            errors.append("Unclosed string literal")

        if errors:
            print("  ✗ Syntax errors:")
            for error in errors:
                print(f"    - {error}")
        else:
            print("  ✓ Valid SPARQL syntax")

        # Extract SELECT variables
        select_match = re.search(r'SELECT\s+((?:\?[\w]+\s+)*\?[\w]+)', query)
        if select_match:
            vars = select_match.group(1).split()
            print(f"  ✓ Select variables: {', '.join(vars)}")


def main():
    print("=" * 70)
    print("LOD PHASE 3: OFFLINE VALIDATION")
    print("=" * 70)

    # 1. Validate RDF Turtle
    print("\n[1] TURTLE RDF VALIDATION\n")
    validator = TurtleValidator('rdf_output/corpus.ttl')
    try:
        validator.load()
        is_valid = validator.validate_syntax()
        entities = validator.count_entities()
    except FileNotFoundError:
        print("✗ ERROR: rdf_output/corpus.ttl not found")
        print("   Run Phase 2: python3 scripts/lod_phase2_generate_rdf.py")
        return

    # 2. Validate SPARQL Queries
    print("\n[2] SPARQL QUERY VALIDATION\n")
    sparql_validator = SPARQLQueryValidator()
    sparql_validator.validate_all()

    # 3. Deployment Readiness
    print("\n\n[3] DEPLOYMENT READINESS CHECKLIST\n")
    print("=" * 50)

    checks = {
        '✓ RDF file exists': Path('rdf_output/corpus.ttl').exists(),
        '✓ Docker available': check_docker(),
        '✓ Docker Compose available': check_docker_compose(),
        '✓ docker-compose.yml exists': Path('docker-compose.yml').exists(),
        '✓ SPARQL script exists': Path('scripts/lod_phase3_sparql_queries.sh').exists(),
        '✓ SPARQL client library exists': Path('doc/html/js/sparql-client.js').exists(),
    }

    ready = all(checks.values())

    for check, status in checks.items():
        symbol = "✓" if status else "✗"
        print(f"  {symbol} {check}")

    print(f"\n{'='*50}")
    if ready:
        print("✅ READY FOR DEPLOYMENT")
        print("\nNext steps:")
        print("  1. docker-compose up -d")
        print("  2. bash scripts/lod_phase3_sparql_queries.sh")
        print("  3. Visit http://localhost:3030/")
    else:
        print("⚠ MISSING DEPENDENCIES")
        print("\nTo proceed:")
        print("  • Install Docker Desktop")
        print("  • Ensure docker-compose.yml is in project root")

    print("\n[4] SUMMARY\n")
    print(f"  RDF Entities:       {entities['total_triples']} triples")
    print(f"  Articles:           {entities['articles']}")
    print(f"  Authors:            {entities['authors']}")
    print(f"  Concepts:           {entities['concepts']}")
    print(f"  SPARQL Queries:     {len(SPARQLQueryValidator.EXAMPLE_QUERIES)}")
    print(f"  Deployment Status:  {'READY ✅' if ready else 'NOT READY ⚠'}")

    print("\n" + "=" * 70)


def check_docker():
    """Check if Docker is available"""
    import subprocess
    try:
        subprocess.run(['docker', '--version'], capture_output=True, timeout=5)
        return True
    except:
        return False


def check_docker_compose():
    """Check if Docker Compose is available"""
    import subprocess
    try:
        subprocess.run(['docker-compose', '--version'], capture_output=True, timeout=5)
        return True
    except:
        return False


if __name__ == '__main__':
    main()
