# Linked Open Data (LOD) Transformation Specification
**Status:** SPECIFICATION (implementation roadmap)  
**Date:** 2026-07-15  
**Scope:** Transform rh_corpus_database_complete.json → 5-star LOD resource

---

## Overview

Transform the current JSON corpus (78 articles, 31 authors, 59 knowledge graphs) into a fully standardized, interoperable Linked Open Data (LOD) resource that:

1. **Resolves metadata gaps** (unknown authors, incomplete years, duplicates)
2. **Maps to standard ontologies** (BIBO, FOAF, DCTERMS, CITO, SKOS)
3. **Implements persistent HTTP URIs** for all entities
4. **Links to external LOD hubs** (Wikidata, ORCID, DBpedia, arXiv)
5. **Publishes as RDF/Turtle** with SPARQL endpoint

---

## Phase 1: Data Cleansing

### 1.1 Resolve Unknown Authors & Metadata Gaps

**Current Issues:**
- 27 new papers have `"authors": [{"name": "Unknown Author"}]`
- Several papers have partial metadata (e.g., `"year": 20` instead of `2020`)
- Duplicate entries with both complete and incomplete records

**Solution:** API-based enrichment

```python
# Pseudo-algorithm: Crossref/arXiv API lookup
for paper in papers:
    if paper['authors'][0]['name'] == 'Unknown Author':
        # Match local_pdf_path (e.g., "1311.4600v3.pdf") to arXiv ID
        arxiv_id = extract_arxiv_id(paper['local_pdf_path'])
        metadata = fetch_arxiv_api(arxiv_id)
        paper['authors'] = metadata['authors']
        paper['title'] = metadata['title']
        paper['year'] = metadata['published_date'].year
        
    if paper['doi'] is None:
        # Lookup DOI via Crossref API
        metadata = crossref_api.search(paper['title'])
        paper['doi'] = metadata['DOI']
```

**Estimated effort:** 2–4 hours (automated)

---

### 1.2 De-duplicate Entities

**Current state:**
- Some papers appear twice (once complete, once as file-based entry)
- Example: `1111.0931` and `1211.5191` have duplicates

**Solution:** Merge by canonical identifier

```python
# Canonicalize by arxiv_id or DOI
papers_by_id = {}
for paper in all_papers:
    canonical_id = paper.get('arxiv_id') or paper.get('doi') or paper['local_pdf_path']
    if canonical_id in papers_by_id:
        # Merge: prefer non-null fields from complete entry
        papers_by_id[canonical_id] = merge_complete(
            papers_by_id[canonical_id],
            paper
        )
    else:
        papers_by_id[canonical_id] = paper
```

**Estimated effort:** 1 hour

---

### 1.3 Normalize Implicit Data Types

**Issues:**
- Incomplete years (`"year": 19` or `20`)
- Birth years with placeholders
- Missing relevance scores

**Solution:** Validation + defaults

```python
for paper in papers:
    # Fix malformed years
    if len(str(paper['year'])) < 4:
        # Guess based on arxiv_id (format: YYMM.XXXXX)
        paper['year'] = infer_year_from_arxiv_id(paper['arxiv_id'])
    
    # Ensure relevance_score in [0, 1]
    if 'relevance_score' not in paper or paper['relevance_score'] is None:
        paper['relevance_score'] = 0.5  # default: moderate relevance
```

**Estimated effort:** 30 minutes

---

## Phase 2: Ontology Mapping

### 2.1 Bibliographic Data (Articles)

**RDF Classes & Properties:**

| JSON Field | RDF Property | Ontology | Range |
|-----------|--|-----|---------|
| `id` | `dcterms:identifier` | DCTERMS | `xsd:string` |
| `title` | `dcterms:title` | DCTERMS | `rdf:langString` |
| `authors` | `dcterms:creator` | DCTERMS | `foaf:Person` (ordered list) |
| `year` | `dcterms:issued` | DCTERMS | `xsd:gYear` |
| `doi` | `bibo:doi` | BIBO | `xsd:string` |
| `arxiv_id` | `bibo:arxivId` or custom | BIBO | `xsd:string` |
| `local_pdf_path` | `schema:downloadUrl` | schema.org | `xsd:anyURI` |
| `role_in_project` | `custom:projectRole` | Custom | `xsd:string` |

**Example Turtle:**

```turtle
@prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
@prefix dcterms: <http://purl.org/dc/terms/> .
@prefix bibo: <http://purl.org/ontology/bibo/> .
@prefix foaf: <http://xmlns.com/foaf/0.1/> .
@prefix schema: <https://schema.org/> .
@prefix rh: <http://data.rh-corpus.org/> .

# Article
rh:article_2607.09797
    a bibo:AcademicArticle ;
    dcterms:title "Recent Advances in RH Approximations"@en ;
    dcterms:creator rh:author_unknown_2607_09797 ;  # Linked to author entity
    dcterms:issued "2026"^^xsd:gYear ;
    bibo:arxivId "2607.09797" ;
    rh:projectRole "H15" ;
    schema:downloadUrl <file:///papers/2607.09797v1.pdf> ;
    rdf:comment "Classified as part of H15 (Möbius cancellation) research track"@en .
```

---

### 2.2 Author Entities

**RDF Classes & Properties:**

| JSON Field | RDF Property | Ontology | Range |
|-----------|--|-----|---------|
| `name` | `foaf:name` | FOAF | `xsd:string` |
| `birth_year` | `foaf:birthday` | FOAF | `xsd:gYear` |
| `affiliation` | `foaf:workplaceHomepage` | FOAF | `xsd:anyURI` |
| (none) | `owl:sameAs` | OWL | ORCID/Wikidata URI |

**Example:**

```turtle
rh:author_hadamard
    a foaf:Person ;
    foaf:name "Jacques Hadamard" ;
    foaf:birthday "1865"^^xsd:gYear ;
    owl:sameAs <https://orcid.org/0000-0000-0000-0000> ;  # ORCID
    owl:sameAs <https://www.wikidata.org/wiki/Q164425> ;  # Wikidata
    foaf:workplaceHomepage <https://en.wikipedia.org/wiki/Jacques_Hadamard> .
```

---

### 2.3 Mathematical Concepts & Theorems

**Use SKOS + DoCO:**

| Concept | RDF Class | Ontology | Properties |
|---------|-----------|----------|-----------|
| Mathematical technique | `skos:Concept` | SKOS | `skos:prefLabel`, `skos:definition`, `skos:broader`, `skos:related` |
| Theorem/main result | `doco:Theorem` | DoCO | `doco:describes`, `dcterms:subject` |
| Key novelty | `doco:Contribution` | DoCO | `dcterms:description`, `cito:citesAsAuthority` |

**Example:**

```turtle
rh:concept_fourier_analysis
    a skos:Concept ;
    skos:prefLabel "Fourier Analysis"@en ;
    skos:definition "Mathematical technique for decomposing functions..."@en ;
    owl:sameAs <https://www.wikidata.org/wiki/Q207849> ;  # Wikidata
    skos:broader rh:concept_harmonic_analysis .

rh:theorem_hadamard_zero_free
    a doco:Theorem ;
    dcterms:title "Hadamard's Zero-Free Region for ζ(s)"@en ;
    doco:describes rh:concept_zero_free_region ;
    cito:citesAsAuthority rh:article_hadamard_1896 .
```

---

### 2.4 Paper Connections (Citation Typing)

**Use CiTO (Citation Typing Ontology):**

```turtle
rh:article_A cito:citesAsAuthority rh:article_B .    # Cites for foundational authority
rh:article_A cito:extends rh:article_B .             # Extends/improves the work
rh:article_A cito:usesMethodIn rh:article_B .        # Uses method from article B
rh:article_A cito:obtainsSupportFrom rh:article_B .  # Supported by article B's results
```

---

### 2.5 Formalization Readiness

**Custom namespace for Lean formalization metadata:**

```turtle
@prefix form: <http://data.rh-corpus.org/formalism/> .

rh:article_vasyunin_1995
    form:formalizable true ;
    form:readiness "partial" ;  # not-started | partial | complete
    form:estimatedEffort "4 weeks" ;
    form:leanProofPath "mathlib/NBMellinTools/NB2BaseMellin.lean" ;
    form:axiomCount 0 ;
    form:sorryCount 0 ;
    form:buildJobsVerified 8484 ;
    form:linkedToProof rh:proof_vasyunin_mellin_identity .

rh:proof_vasyunin_mellin_identity
    a form:LeanProof ;
    dcterms:title "Mellin transform of base period function"@en ;
    form:codeLength 1050 ;  # KB
    form:theorem "ℳ(ρ_base)(s) = -ζ(s)/s for 0 < Re(s) < 1" ;
    form:status "verified" .
```

---

## Phase 3: URI Minting & External Linking

### 3.1 Internal URI Scheme

**Persistent identifiers for all entities:**

```
Articles:    http://data.rh-corpus.org/article/{arxiv_id or doi}
Authors:     http://data.rh-corpus.org/author/{lastname-firstname}
Concepts:    http://data.rh-corpus.org/concept/{url_slug}
Theorems:    http://data.rh-corpus.org/theorem/{slug}
Proofs:      http://data.rh-corpus.org/proof/{slug}
Insights:    http://data.rh-corpus.org/insight/{id}
```

**Examples:**

```
http://data.rh-corpus.org/article/2607.09797
http://data.rh-corpus.org/article/doi_10.1234_example
http://data.rh-corpus.org/author/hadamard-jacques
http://data.rh-corpus.org/concept/mellin-transform
http://data.rh-corpus.org/theorem/nyman-beurling-equivalence
http://data.rh-corpus.org/proof/nb5-functional-closure
```

---

### 3.2 External LOD Linking

**Link all entities to authoritative external sources:**

| Entity Type | External Source | Property | Example |
|-----------|-----------------|----------|---------|
| Authors | ORCID | `owl:sameAs` | https://orcid.org/0000-0002-XXXX-XXXX |
| Authors | Wikidata | `owl:sameAs` | https://www.wikidata.org/wiki/Q164425 |
| Articles | arXiv | `dcterms:source` | https://arxiv.org/abs/2607.09797 |
| Articles | DOI | `dcterms:identifier` | https://doi.org/10.XXXX/XXXX |
| Concepts | Wikidata | `owl:sameAs` | https://www.wikidata.org/wiki/Q18816 |
| Concepts | DBpedia | `owl:sameAs` | https://dbpedia.org/resource/Riemann_zeta_function |
| Math concepts | Math Subject Classification | `dcterms:subject` | http://www.ams.org/msc/msc2020.html?t=11M26 |

**Example Wikidata integration:**

```turtle
rh:article_2607.09797
    dcterms:subject wd:Q18816 ;           # Riemann zeta function (Wikidata)
    dcterms:subject wd:Q131187 ;          # Prime number theorem (Wikidata)
    dcterms:subject msc:11M26 ;           # MSC: Nonreal zeros, Riemann Hypothesis
    dcterms:isPartOf wd:Q123456 .         # Part of Riemann Hypothesis research
```

---

## Phase 4: RDF Generation & Publishing

### 4.1 Data Pipeline Architecture

```
rh_corpus_database_complete.json
        │
        ▼ (RML Mapping)
    [mapping.rml.ttl]
        │
        ▼ (RML Processor or Custom Script)
    ┌─────────────────────────────┐
    │  Triple Generation (TTL)    │
    │  - articles.ttl (400 KB)    │
    │  - authors.ttl (50 KB)      │
    │  - concepts.ttl (100 KB)    │
    │  - theorems.ttl (80 KB)     │
    │  - connections.ttl (60 KB)  │
    └─────────────────────────────┘
        │
        ▼ (Bulk Load)
    ┌─────────────────────────────┐
    │   Graph Database Server     │
    │  (GraphDB / Jena / BGP)     │
    └─────────────────────────────┘
        │
        ├──────────────────────────────────────┐
        │                                      │
        ▼                                      ▼
    SPARQL Endpoint               Linked Data Frontend
    (REST API)                    (Content Negotiation)
    
    GET /sparql?query=...         GET /article/2607.09797
    → JSON/XML/TTL                → RDF/HTML (HTML-RDFa)
```

---

### 4.2 RML Mapping Rules

**Sample RML (RDF Mapping Language) mapping.rml.ttl:**

```turtle
@prefix rml: <http://semweb.mmlab.be/ns/rml#> .
@prefix rr: <http://www.w3.org/ns/r2rml#> .
@prefix ql: <http://semweb.mmlab.be/ns/ql#> .
@prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> .
@prefix dcterms: <http://purl.org/dc/terms/> .
@prefix foaf: <http://xmlns.com/foaf/0.1/> .
@prefix bibo: <http://purl.org/ontology/bibo/> .
@prefix rh: <http://data.rh-corpus.org/> .

# --- Mapping: articles array to RDF ---
<#ArticleMapping>
    a rr:TriplesMap ;
    rml:logicalSource [
        rml:source "rh_corpus_database_complete.json" ;
        rml:referenceFormulation ql:JSONPath ;
        rml:iterator "$.articles[*]"
    ] ;
    rr:subjectMap [
        rr:template "http://data.rh-corpus.org/article/{id}"
    ] ;
    rr:predicateObjectMap [
        rr:predicate dcterms:title ;
        rr:objectMap [ rml:reference "title" ]
    ] ;
    rr:predicateObjectMap [
        rr:predicate dcterms:issued ;
        rr:objectMap [ 
            rml:reference "year" ;
            rr:datatype <http://www.w3.org/2001/XMLSchema#gYear>
        ]
    ] ;
    rr:predicateObjectMap [
        rr:predicate dcterms:creator ;
        rr:objectMap [
            rr:parentTriplesMap <#AuthorMapping> ;
            rr:joinCondition [
                rr:child "authors[0].id" ;
                rr:parent "id"
            ]
        ]
    ] .

# --- Mapping: authors array to foaf:Person ---
<#AuthorMapping>
    a rr:TriplesMap ;
    rml:logicalSource [
        rml:source "rh_corpus_database_complete.json" ;
        rml:referenceFormulation ql:JSONPath ;
        rml:iterator "$.papers[*].authors[*]"
    ] ;
    rr:subjectMap [
        rr:template "http://data.rh-corpus.org/author/{id}"
    ] ;
    rr:predicateObjectMap [
        rr:predicate foaf:name ;
        rml:reference "name"
    ] .
```

---

### 4.3 SPARQL Endpoint Setup

**Example queries enabled by LOD:**

```sparql
# Query 1: Find all papers authored by Hadamard that cite the Riemann zeta function
PREFIX dcterms: <http://purl.org/dc/terms/>
PREFIX foaf: <http://xmlns.com/foaf/0.1/>
PREFIX wd: <https://www.wikidata.org/wiki/>

SELECT ?article ?title ?year WHERE {
    ?article dcterms:creator ?author ;
             dcterms:title ?title ;
             dcterms:issued ?year ;
             dcterms:subject wd:Q18816 .  # Riemann zeta function
    ?author foaf:name "Jacques Hadamard" .
}
ORDER BY ?year DESC

# Query 2: Find papers using Fourier analysis that are cited by modern H15 research
PREFIX cito: <http://purl.org/spar/cito/>
PREFIX skos: <http://www.w3.org/2004/02/skos/core#>

SELECT ?ancient ?modern ?technique WHERE {
    ?modern rh:projectRole "H15" ;
            cito:citesAsAuthority ?ancient .
    ?ancient dcterms:subject ?concept .
    ?concept skos:prefLabel ?technique .
    FILTER(REGEX(?technique, "Fourier"))
}

# Query 3: Show all papers with formal proofs in Lean, sorted by build jobs
PREFIX form: <http://data.rh-corpus.org/formalism/>

SELECT ?article ?title ?buildJobs ?axiomCount WHERE {
    ?article dcterms:title ?title ;
             form:leanProofPath ?path ;
             form:buildJobsVerified ?buildJobs ;
             form:axiomCount ?axiomCount .
}
ORDER BY DESC(?buildJobs)
```

---

## Phase 5: Infrastructure & Deployment

### 5.1 Technology Stack

**Option A: Lightweight (Recommended for initial deployment)**
- **Triplestore:** Apache Jena Fuseki (lightweight, open-source SPARQL server)
- **Graph DB:** TDB2 (built into Jena)
- **Frontend:** LodView (automatic Linked Data browser)
- **Deployment:** Docker container + nginx reverse proxy
- **Backup:** TTL files stored in git/archive

**Option B: Enterprise-Grade**
- **Triplestore:** GraphDB (commercial, but open-core available)
- **Frontend:** VoID/LODLaundromat + Datahub.io
- **Deployment:** Kubernetes cluster
- **Analytics:** SPARQL query logs + usage statistics

### 5.2 Docker Configuration

```dockerfile
FROM openjdk:11-slim

# Install Jena Fuseki
RUN wget https://archive.apache.org/dist/jena/binaries/apache-jena-fuseki-4.5.0.tar.gz && \
    tar -xzf apache-jena-fuseki-4.5.0.tar.gz && \
    mv apache-jena-fuseki-4.5.0 /opt/fuseki

# Copy RDF data
COPY data/*.ttl /opt/fuseki/run/

# Expose SPARQL endpoint
EXPOSE 3030

CMD ["/opt/fuseki/fuseki-server", "--loc=/opt/fuseki/run", "/rh"]
```

**Run:** `docker run -p 3030:3030 rh-lod:latest`

**Access:**
- SPARQL Endpoint: `http://localhost:3030/rh/sparql`
- Linked Data Browser: `http://localhost:3030/rh/resource`

---

## Implementation Roadmap

| Phase | Task | Timeline | Effort |
|-------|------|----------|--------|
| **1** | Data cleansing (authors, years, dedup) | Week 1 | 8 hours |
| **2** | Ontology mapping (BIBO, FOAF, DCTERMS, CITO) | Week 2 | 16 hours |
| **3** | URI minting + external linking (Wikidata, ORCID) | Week 2 | 12 hours |
| **4** | RML mapping rules + RDF generation | Week 3 | 16 hours |
| **5** | SPARQL endpoint setup (Jena Fuseki) | Week 3 | 8 hours |
| **6** | Linked Data frontend (LodView) + validation | Week 4 | 12 hours |
| **7** | Documentation + deployment guide | Week 4 | 8 hours |
| **8** | Public launch + query examples | Week 4 | 4 hours |
| **TOTAL** | | **4 weeks** | **84 hours** |

---

## Success Criteria

✅ **5-Star LOD Achievement:**

1. ✅ **Structured Data:** All 78 articles, 31 authors, 59 concepts mapped to RDF
2. ✅ **Machine-Readable:** RDF/Turtle serialization complete
3. ✅ **Non-Proprietary Ontologies:** BIBO, FOAF, DCTERMS, CITO, SKOS (all W3C standards)
4. ✅ **Linked Data URIs:** Every entity has a resolvable HTTP URI
5. ✅ **External Links:** All entities linked to Wikidata, ORCID, DBpedia, arXiv where applicable
6. ✅ **SPARQL Endpoint:** Public query interface at /sparql
7. ✅ **Content Negotiation:** RDF/HTML/JSON-LD returned based on Accept header
8. ✅ **VoID Description:** Dataset metadata published in VoID format

---

## Next Steps

1. **Prioritize:** Start with Phase 1 (data cleansing) for quick wins
2. **Tool Selection:** Choose between lightweight (Jena) vs. enterprise (GraphDB) setup
3. **Community Feedback:** Share RML mapping with LOD/Semantic Web community for review
4. **Beta Release:** Publish initial RDF dump + SPARQL endpoint for feedback
5. **Iterate:** Refine ontology mappings based on use cases

---

## References

- **W3C Semantic Web Standards:** https://www.w3.org/standards/semanticweb/
- **Linked Open Data Cloud:** https://lod-cloud.net/
- **BIBO Ontology:** https://purl.org/ontology/bibo/
- **RML Specification:** http://rml.io/spec.html
- **Wikidata API:** https://www.wikidata.org/wiki/Wikidata:Main_Page
- **CiTO Ontology:** http://purl.org/spar/cito/

---

**Status:** READY FOR IMPLEMENTATION ✅
