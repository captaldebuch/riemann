# Phase 3: SPARQL Endpoint Deployment Guide
**Status:** Ready for Deployment  
**Prerequisites:** Docker Desktop + Docker Compose  
**Estimated Time:** 30 minutes (setup) + 15 minutes (testing)

---

## Prerequisites Check

```bash
# 1. Check Docker installation
docker --version
# Expected: Docker version 20.10+

# 2. Check Docker Compose
docker-compose --version
# Expected: Docker Compose version 1.29+

# 3. Ensure RDF file exists
ls -lh rdf_output/corpus.ttl
# Expected: ~50KB+ file

# 4. Ensure scripts are executable
chmod +x scripts/lod_phase3_sparql_queries.sh
```

---

## Step 1: Start SPARQL Endpoint (5 minutes)

### Option A: Using Docker Compose (Recommended)

```bash
# Navigate to project root
cd /path/to/riemann/project

# Start Jena Fuseki in background
docker-compose up -d

# Check status
docker-compose ps
# Should show: rh-sparql-server (Up)

# View logs (optional, helpful for debugging)
docker-compose logs -f jena-fuseki
# Wait for: "Started FusekiServer" message
```

### Option B: Manual Docker Run

```bash
# If docker-compose fails, use direct docker command
docker run -d \
  --name rh-sparql-server \
  -p 3030:3030 \
  -v $(pwd)/rdf_output:/rdf \
  -v $(pwd)/fuseki_data:/jena/run \
  stain/jena-fuseki:4.8.0 \
  /jena/fuseki-server \
  --loc=/jena/run/tdb \
  /rh

# Check logs
docker logs -f rh-sparql-server
```

### Verification

```bash
# Check if port 3030 is listening
lsof -i :3030

# Or test with curl
curl -s http://localhost:3030/ | head -20
# Should return HTML response
```

---

## Step 2: Load RDF Data (5 minutes)

### Method 1: Using curl (Simplest)

```bash
# Upload RDF via HTTP PUT
curl -X PUT \
  --data-binary @rdf_output/corpus.ttl \
  -H "Content-Type: text/turtle" \
  http://localhost:3030/rh/data?default

# Expected response: HTTP 200 or 201
```

### Method 2: Using SPARQL Update

```bash
# Create file: load_rdf.sparql
cat > load_rdf.sparql << 'EOF'
LOAD <file:///rdf/corpus.ttl> INTO <http://example.org/rh>
EOF

curl -X POST \
  --data-urlencode "update@load_rdf.sparql" \
  http://localhost:3030/rh/update
```

### Method 3: Automated Script

```bash
# Run the provided test script
bash scripts/lod_phase3_sparql_queries.sh
```

### Verification

```bash
# Check triple count
curl -s -X GET \
  --data-urlencode "query=SELECT (COUNT(*) AS ?count) WHERE { ?s ?p ?o }" \
  http://localhost:3030/rh/query?output=json | jq '.results.bindings'

# Expected: Multiple thousands of triples
```

---

## Step 3: Test SPARQL Queries (10 minutes)

### Test Query 1: Count Articles

```bash
curl -s -X GET \
  --data-urlencode "query=PREFIX bibo: <http://purl.org/ontology/bibo/> SELECT (COUNT(?article) AS ?count) WHERE { ?article a bibo:AcademicArticle . }" \
  http://localhost:3030/rh/query?output=json | jq '.'

# Expected output:
# {
#   "head": { "vars": ["count"] },
#   "results": { "bindings": [{ "count": { "type": "literal", "value": "78" } }] }
# }
```

### Test Query 2: Papers by Year

```bash
curl -s -X GET \
  --data-urlencode "query=PREFIX dcterms: <http://purl.org/dc/terms/> PREFIX bibo: <http://purl.org/ontology/bibo/> SELECT ?year (COUNT(?article) AS ?count) WHERE { ?article a bibo:AcademicArticle ; dcterms:issued ?year . } GROUP BY ?year ORDER BY DESC(?year) LIMIT 10" \
  http://localhost:3030/rh/query?output=json | jq '.results.bindings'

# Expected: Year → count pairs, sorted by year DESC
```

### Test Query 3: H15 Papers

```bash
curl -s -X GET \
  --data-urlencode "query=PREFIX dcterms: <http://purl.org/dc/terms/> PREFIX rh: <http://data.rh-corpus.org/> PREFIX bibo: <http://purl.org/ontology/bibo/> SELECT ?title ?year WHERE { ?article a bibo:AcademicArticle ; dcterms:title ?title ; dcterms:issued ?year ; rh:projectRole \"H15\" . } LIMIT 5" \
  http://localhost:3030/rh/query?output=json | jq '.results.bindings'

# Expected: 5 H15 papers
```

### Run All Tests

```bash
# Use the provided test script
bash scripts/lod_phase3_sparql_queries.sh

# This runs 5 example queries automatically and reports results
```

---

## Step 4: Access SPARQL Interface

### Web UI (Optional)

Visit: **http://localhost:3030/**

Features:
- Query builder
- Results viewer
- Dataset statistics
- SPARQL editor

### SPARQL Endpoint

Direct endpoint: **http://localhost:3030/rh/query**

Example:
```bash
# Simple test
curl "http://localhost:3030/rh/query?query=SELECT%20*%20WHERE%20%7B%20%3Fs%20%3Fp%20%3Fo%20%7D%20LIMIT%201"
```

---

## Performance Validation

### Query Response Time

```bash
# Measure query time
time curl -s -X GET \
  --data-urlencode "query=PREFIX bibo: <http://purl.org/ontology/bibo/> SELECT ?title WHERE { ?article a bibo:AcademicArticle ; dcterms:title ?title . } LIMIT 1000" \
  http://localhost:3030/rh/query?output=json > /dev/null

# Expected: < 100ms total time
```

### Concurrent Queries

```bash
# Test 5 concurrent queries
for i in {1..5}; do
  curl -s -X GET \
    --data-urlencode "query=SELECT (COUNT(*) AS ?c) WHERE { ?s ?p ?o }" \
    http://localhost:3030/rh/query?output=json &
done
wait

# All should complete without errors
```

---

## Troubleshooting

### Problem: Port 3030 Already in Use

```bash
# Find process using port
lsof -i :3030

# Kill process
kill -9 <PID>

# Or use different port in docker-compose.yml
# Change: ports: ["3030:3030"] → ["3031:3030"]
```

### Problem: RDF Data Not Loading

```bash
# Check Fuseki logs
docker logs rh-sparql-server

# Verify RDF syntax
# Check file size
ls -lh rdf_output/corpus.ttl

# Test RDF validity (if rapper installed)
rapper -g rdf_output/corpus.ttl

# Manual upload with verbose output
curl -v -X PUT \
  --data-binary @rdf_output/corpus.ttl \
  -H "Content-Type: text/turtle" \
  http://localhost:3030/rh/data?default
```

### Problem: SPARQL Queries Timeout

```bash
# Check Fuseki memory usage
docker stats rh-sparql-server

# Increase memory in docker-compose.yml
# Add to environment: FUSEKI_OPTS: "--mem --min-jvm-size=512M --max-jvm-size=2G"

# Restart
docker-compose restart jena-fuseki
```

---

## Integration with Website (Phase 4)

Once SPARQL endpoint is running:

```javascript
// In doc/html/js/sparql-client.js
// Update endpoint URL (if not localhost:3030):

const SPARQL_ENDPOINT = "http://your-domain:3030/rh/query";

// In app.js
// Import and use:
const sparql = new RHSPARQLClient();

// Example: Search papers
const papers = await sparql.searchArticles("Riemann");

// Example: Get H15 papers
const h15 = await sparql.papersByRole('H15');

// Example: Get statistics
const stats = await sparql.statsByYear();
```

---

## Deployment Checklist

- [ ] Docker Desktop installed and running
- [ ] Docker Compose installed
- [ ] `docker ps` shows no errors
- [ ] `rdf_output/corpus.ttl` exists
- [ ] `docker-compose up -d` succeeds
- [ ] `docker ps` shows `rh-sparql-server` (Up)
- [ ] `curl http://localhost:3030/` returns HTML
- [ ] RDF data uploaded (HTTP 200/201)
- [ ] Test Query 1 returns 78 articles
- [ ] Test Query 2 returns year grouping
- [ ] Test Query 3 returns H15 papers
- [ ] Response time < 100ms
- [ ] Web UI accessible at http://localhost:3030/

---

## Production Deployment (Optional)

For production deployment:

```bash
# Use HTTPS and authentication
# Update docker-compose.yml:

services:
  jena-fuseki:
    environment:
      FUSEKI_OPTS: "--mem --secure"
    ports:
      - "443:8443"  # HTTPS
```

For cloud deployment (AWS, Azure, GCP):

```bash
# Push Docker image to registry
docker tag rh-sparql stain/jena-fuseki:rh-corpus
docker push your-registry/rh-sparql:latest

# Deploy via Kubernetes/Docker Swarm
# (See deployment manifests in docs/)
```

---

## Next Steps (Phase 4)

Once SPARQL endpoint is confirmed working:

1. **Integrate into website:**
   - Load `sparql-client.js` in index.html
   - Update `app.js` to use SPARQL queries

2. **Add SPARQL search:**
   - Replace JSON search with SPARQL queries
   - Implement real-time filtering

3. **Deploy LodView:**
   - Optional: Automatic RDF-to-HTML conversion
   - Content negotiation: RDF/HTML/JSON-LD

4. **Test end-to-end:**
   - Test searches in SPA
   - Verify SPARQL response times
   - Check browser console for errors

---

## Support & Debugging

**Jena Fuseki Documentation:**
https://jena.apache.org/documentation/fuseki2/

**Docker Image:**
https://hub.docker.com/r/stain/jena-fuseki/

**SPARQL Tutorial:**
https://www.w3.org/2009/sparql/wiki/Main_Page

**Questions?**
Check `LOD_TRANSFORMATION_PROGRESS.md` for detailed progress status

---

**Status:** Ready for deployment ✅  
**Estimated Time to Production:** ~1 hour (setup + testing + integration)  
**Target Completion:** 2026-07-31 (Week 4)
