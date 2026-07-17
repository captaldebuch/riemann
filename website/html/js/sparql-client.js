/**
 * SPARQL Client for RH Corpus
 * Phase 4: Website Integration - LOD Query Support
 *
 * Enables direct SPARQL queries against the RH graph database
 * Provides high-level query builders for common use cases
 */

const SPARQL_ENDPOINT = "http://localhost:3030/rh/query";

class RHSPARQLClient {
    constructor(endpoint = SPARQL_ENDPOINT) {
        this.endpoint = endpoint;
        this.timeout = 10000; // 10 second timeout
    }

    /**
     * Execute a SPARQL query
     * @param {string} query - SPARQL query string
     * @returns {Promise<Object>} Query results
     */
    async query(query) {
        try {
            const response = await fetch(this.endpoint, {
                method: 'GET',
                headers: {
                    'Accept': 'application/sparql-results+json'
                },
                body: new URLSearchParams({
                    'query': query
                })
            });

            if (!response.ok) {
                throw new Error(`SPARQL query failed: HTTP ${response.status}`);
            }

            return await response.json();
        } catch (error) {
            console.error('SPARQL query error:', error);
            return { results: { bindings: [] } };
        }
    }

    /**
     * Search articles by title
     * @param {string} searchTerm - Search term
     * @returns {Promise<Array>} Matching articles
     */
    async searchArticles(searchTerm) {
        const query = `
PREFIX dcterms: <http://purl.org/dc/terms/>
PREFIX bibo: <http://purl.org/ontology/bibo/>

SELECT ?articleId ?title ?year
WHERE {
    ?article a bibo:AcademicArticle ;
             dcterms:title ?title ;
             dcterms:issued ?year ;
             rdf:ID ?articleId .
    FILTER(CONTAINS(LCASE(?title), LCASE("${searchTerm}")))
}
ORDER BY DESC(?year)
LIMIT 20
        `;

        const result = await this.query(query);
        return result.results.bindings.map(b => ({
            id: b.articleId?.value || '',
            title: b.title?.value || '',
            year: b.year?.value || ''
        }));
    }

    /**
     * Find papers by project role (H15, H14, H13, NB)
     * @param {string} role - Project role
     * @returns {Promise<Array>} Papers with that role
     */
    async papersByRole(role) {
        const query = `
PREFIX dcterms: <http://purl.org/dc/terms/>
PREFIX rh: <http://data.rh-corpus.org/>
PREFIX bibo: <http://purl.org/ontology/bibo/>

SELECT ?title ?year ?relevance
WHERE {
    ?article a bibo:AcademicArticle ;
             dcterms:title ?title ;
             dcterms:issued ?year ;
             rh:projectRole "${role}" ;
             rh:relevanceScore ?relevance .
}
ORDER BY DESC(?relevance) DESC(?year)
        `;

        const result = await this.query(query);
        return result.results.bindings.map(b => ({
            title: b.title?.value || '',
            year: b.year?.value || '',
            relevance: parseFloat(b.relevance?.value) || 0
        }));
    }

    /**
     * Find papers by concept/tag
     * @param {string} concept - Concept name
     * @returns {Promise<Array>} Papers related to concept
     */
    async papersByConc (concept) {
        const query = `
PREFIX dcterms: <http://purl.org/dc/terms/>
PREFIX skos: <http://www.w3.org/2004/02/skos/core#>
PREFIX bibo: <http://purl.org/ontology/bibo/>

SELECT ?title ?year ?conceptLabel
WHERE {
    ?article a bibo:AcademicArticle ;
             dcterms:title ?title ;
             dcterms:issued ?year ;
             dcterms:subject ?conceptUri .
    ?conceptUri a skos:Concept ;
                skos:prefLabel ?conceptLabel .
    FILTER(CONTAINS(LCASE(?conceptLabel), LCASE("${concept}")))
}
ORDER BY DESC(?year)
LIMIT 20
        `;

        const result = await this.query(query);
        return result.results.bindings.map(b => ({
            title: b.title?.value || '',
            year: b.year?.value || '',
            concept: b.conceptLabel?.value || ''
        }));
    }

    /**
     * Find papers by author
     * @param {string} authorName - Author name
     * @returns {Promise<Array>} Papers by author
     */
    async papersByAuthor(authorName) {
        const query = `
PREFIX dcterms: <http://purl.org/dc/terms/>
PREFIX foaf: <http://xmlns.com/foaf/0.1/>
PREFIX bibo: <http://purl.org/ontology/bibo/>

SELECT ?title ?year
WHERE {
    ?article a bibo:AcademicArticle ;
             dcterms:title ?title ;
             dcterms:issued ?year ;
             dcterms:creator ?author .
    ?author foaf:name ?name .
    FILTER(CONTAINS(LCASE(?name), LCASE("${authorName}")))
}
ORDER BY DESC(?year)
        `;

        const result = await this.query(query);
        return result.results.bindings.map(b => ({
            title: b.title?.value || '',
            year: b.year?.value || ''
        }));
    }

    /**
     * Get statistics: papers per year
     * @returns {Promise<Array>} Year → count mapping
     */
    async statsByYear() {
        const query = `
PREFIX dcterms: <http://purl.org/dc/terms/>
PREFIX bibo: <http://purl.org/ontology/bibo/>

SELECT ?year (COUNT(?article) AS ?count)
WHERE {
    ?article a bibo:AcademicArticle ;
             dcterms:issued ?year .
}
GROUP BY ?year
ORDER BY DESC(?year)
        `;

        const result = await this.query(query);
        return result.results.bindings.map(b => ({
            year: b.year?.value || '',
            count: parseInt(b.count?.value) || 0
        }));
    }

    /**
     * Get statistics: papers per role
     * @returns {Promise<Array>} Role → count mapping
     */
    async statsByRole() {
        const query = `
PREFIX rh: <http://data.rh-corpus.org/>
PREFIX bibo: <http://purl.org/ontology/bibo/>

SELECT ?role (COUNT(?article) AS ?count)
WHERE {
    ?article a bibo:AcademicArticle ;
             rh:projectRole ?role .
}
GROUP BY ?role
ORDER BY DESC(?count)
        `;

        const result = await this.query(query);
        return result.results.bindings.map(b => ({
            role: b.role?.value || 'General',
            count: parseInt(b.count?.value) || 0
        }));
    }

    /**
     * Get top concepts by frequency
     * @param {number} limit - Number of concepts to return
     * @returns {Promise<Array>} Concepts with counts
     */
    async topConcepts(limit = 20) {
        const query = `
PREFIX dcterms: <http://purl.org/dc/terms/>
PREFIX skos: <http://www.w3.org/2004/02/skos/core#>
PREFIX bibo: <http://purl.org/ontology/bibo/>

SELECT ?concept (COUNT(?article) AS ?count)
WHERE {
    ?article a bibo:AcademicArticle ;
             dcterms:subject ?conceptUri .
    ?conceptUri skos:prefLabel ?concept .
}
GROUP BY ?concept
ORDER BY DESC(?count)
LIMIT ${limit}
        `;

        const result = await this.query(query);
        return result.results.bindings.map(b => ({
            concept: b.concept?.value || '',
            count: parseInt(b.count?.value) || 0
        }));
    }

    /**
     * Get author statistics
     * @param {number} limit - Number of authors to return
     * @returns {Promise<Array>} Authors with paper counts
     */
    async topAuthors(limit = 20) {
        const query = `
PREFIX dcterms: <http://purl.org/dc/terms/>
PREFIX foaf: <http://xmlns.com/foaf/0.1/>
PREFIX bibo: <http://purl.org/ontology/bibo/>

SELECT ?author (COUNT(?article) AS ?count)
WHERE {
    ?article a bibo:AcademicArticle ;
             dcterms:creator ?authorUri .
    ?authorUri foaf:name ?author .
}
GROUP BY ?author
ORDER BY DESC(?count)
LIMIT ${limit}
        `;

        const result = await this.query(query);
        return result.results.bindings.map(b => ({
            author: b.author?.value || '',
            count: parseInt(b.count?.value) || 0
        }));
    }
}

// Export for use in other modules
if (typeof module !== 'undefined' && module.exports) {
    module.exports = RHSPARQLClient;
}
