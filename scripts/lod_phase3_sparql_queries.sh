#!/bin/bash
# LOD Phase 3: SPARQL Endpoint Setup and Example Queries
# Run after docker-compose is started

set -e

FUSEKI_URL="http://localhost:3030/rh"
RDF_FILE="rdf_output/corpus.ttl"

echo "========================================================================"
echo "LOD PHASE 3: SPARQL ENDPOINT SETUP"
echo "========================================================================"
echo ""

# ========================================================================
# Step 1: Load RDF Data into Jena Fuseki
# ========================================================================

echo "[1] Loading RDF data into SPARQL endpoint..."

# Check if server is running
if ! curl -s "$FUSEKI_URL/query" > /dev/null; then
    echo "❌ SPARQL endpoint not responding at $FUSEKI_URL"
    echo "   Make sure to run: docker-compose up -d"
    exit 1
fi

echo "    ✓ SPARQL endpoint is running"
echo ""

# Upload RDF data using PUT to the graph store
echo "    Uploading $RDF_FILE..."
HTTP_CODE=$(curl -s -o /dev/null -w "%{http_code}" -X PUT \
    --data-binary @"$RDF_FILE" \
    -H "Content-Type: text/turtle" \
    "$FUSEKI_URL/data?default")

if [ "$HTTP_CODE" = "200" ] || [ "$HTTP_CODE" = "201" ]; then
    echo "    ✓ RDF data loaded successfully (HTTP $HTTP_CODE)"
else
    echo "    ⚠ Upload status: HTTP $HTTP_CODE (may still be loading)"
fi

echo ""
echo "[2] Waiting for data to be indexed..."
sleep 3

# ========================================================================
# Step 2: Test SPARQL Queries
# ========================================================================

echo "[3] Testing SPARQL Queries..."
echo ""

# Query function
run_query() {
    local name="$1"
    local query="$2"

    echo "    Query: $name"
    echo "    ────────────────────────────────────────────"

    RESULT=$(curl -s -X GET \
        --data-urlencode "query=$query" \
        -H "Accept: application/sparql-results+json" \
        "$FUSEKI_URL/query")

    # Check if result contains bindings
    if echo "$RESULT" | grep -q '"bindings"'; then
        COUNT=$(echo "$RESULT" | grep -o '"x":"' | wc -l)
        echo "    Results: $(echo "$RESULT" | jq '.results.bindings | length' 2>/dev/null || echo '?') rows"
    else
        echo "    Error: No results returned"
    fi

    echo ""
}

# ========================================================================
# QUERY 1: Count all articles
# ========================================================================

QUERY_1='
PREFIX bibo: <http://purl.org/ontology/bibo/>
SELECT (COUNT(?article) AS ?count)
WHERE {
    ?article a bibo:AcademicArticle .
}
'

run_query "Count All Articles" "$QUERY_1"

# ========================================================================
# QUERY 2: Articles by year
# ========================================================================

QUERY_2='
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
'

run_query "Articles by Year" "$QUERY_2"

# ========================================================================
# QUERY 3: H15 papers with authors
# ========================================================================

QUERY_3='
PREFIX dcterms: <http://purl.org/dc/terms/>
PREFIX rh: <http://data.rh-corpus.org/>
PREFIX bibo: <http://purl.org/ontology/bibo/>
PREFIX foaf: <http://xmlns.com/foaf/0.1/>
SELECT ?title ?authors
WHERE {
    ?article a bibo:AcademicArticle ;
             dcterms:title ?title ;
             rh:projectRole "H15" ;
             dcterms:creator ?author .
    ?author foaf:name ?authors .
}
LIMIT 5
'

run_query "H15 Papers" "$QUERY_3"

# ========================================================================
# QUERY 4: Papers by concept
# ========================================================================

QUERY_4='
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
'

run_query "Papers by Concept" "$QUERY_4"

# ========================================================================
# QUERY 5: Authors and their paper count
# ========================================================================

QUERY_5='
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
'

run_query "Authors by Paper Count" "$QUERY_5"

# ========================================================================
# Summary
# ========================================================================

echo "========================================================================"
echo "SPARQL ENDPOINT READY"
echo "========================================================================"
echo ""
echo "Access endpoints:"
echo "  • SPARQL Query:  $FUSEKI_URL/query"
echo "  • SPARQL Update: $FUSEKI_URL/update"
echo "  • Linked Data:   $FUSEKI_URL/data"
echo "  • Web UI:        http://localhost:3030"
echo ""
echo "Example curl command:"
echo "  curl -X GET \\"
echo "    --data-urlencode 'query=SELECT ?title WHERE { ?s <http://purl.org/dc/terms/title> ?title . } LIMIT 5' \\"
echo "    http://localhost:3030/rh/query"
echo ""
echo "Stop services:"
echo "  docker-compose down"
echo ""
