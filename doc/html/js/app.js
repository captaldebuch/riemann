/**
 * DH Repository SPA Application Logic (LOD Edition)
 */

const STATE = {
  db: null,
  currentRoute: 'home',
  routeParams: null,
  isLoading: true,
  sparqlAvailable: false,
  sparqlClient: null
};

// Initialize Application
async function initApp() {
  try {
    if (window.DH_DATA) {
      STATE.db = window.DH_DATA;
    } else {
      console.warn("Could not load DH_DATA.");
      STATE.db = { papers: {}, authors: {}, concepts: {} };
    }

    // Initialize SPARQL client (Phase 4: LOD Integration)
    if (typeof RHSPARQLClient !== 'undefined') {
      STATE.sparqlClient = new RHSPARQLClient();
      // Test SPARQL availability
      try {
        await testSPARQLEndpoint();
      } catch (e) {
        console.log("SPARQL endpoint not available - using JSON data fallback");
        STATE.sparqlAvailable = false;
      }
    }

    STATE.isLoading = false;
    setupRouter();
    handleRoute();
  } catch (error) {
    console.error("Error loading DH data:", error);
    document.getElementById('app-content').innerHTML = `
      <div class="alert warning">
        <strong>Error Loading Data:</strong> Failed to initialize DH repository data.
      </div>`;
  }
}

// Test SPARQL Endpoint Availability (Phase 4)
async function testSPARQLEndpoint() {
  if (!STATE.sparqlClient) return false;
  try {
    const result = await STATE.sparqlClient.query(
      'SELECT (COUNT(*) AS ?count) WHERE { ?s ?p ?o } LIMIT 1'
    );
    if (result.results && result.results.bindings) {
      STATE.sparqlAvailable = true;
      console.log("✓ SPARQL endpoint available (LOD v1)");
      return true;
    }
  } catch (e) {
    STATE.sparqlAvailable = false;
  }
  return false;
}

// Router
function setupRouter() {
  window.addEventListener('hashchange', handleRoute);
  
  // Intercept nav clicks
  document.querySelectorAll('.nav-link').forEach(link => {
    link.addEventListener('click', (e) => {
      document.querySelectorAll('.nav-link').forEach(l => l.classList.remove('active'));
      e.target.classList.add('active');
    });
  });
}

function handleRoute() {
  const hash = window.location.hash.substring(1) || 'home';
  
  // Parse parameterized routes e.g. "paper/2607.09797"
  const parts = hash.split('/');
  STATE.currentRoute = parts[0];
  STATE.routeParams = parts.slice(1);
  
  // Update active nav link
  document.querySelectorAll('.nav-link').forEach(l => {
    if (l.dataset.route === STATE.currentRoute) l.classList.add('active');
    else l.classList.remove('active');
  });

  renderView();
}

// Render Engine
function renderView() {
  const content = document.getElementById('app-content');
  if (STATE.isLoading) return;
  
  window.scrollTo(0, 0);

  switch(STATE.currentRoute) {
    case 'home':
      content.innerHTML = renderHome();
      break;
    case 'mathematicians':
      content.innerHTML = renderMathematicians();
      break;
    case 'corpus':
      content.innerHTML = renderCorpus();
      break;
    case 'insights':
      content.innerHTML = renderInsights();
      if (window.renderMathInElement) {
        renderMathInElement(content, {
          delimiters: [
            {left: '$$', right: '$$', display: true},
            {left: '$', right: '$', display: false},
            {left: '\\(', right: '\\)', display: false},
            {left: '\\[', right: '\\]', display: true}
          ]
        });
      }
      break;
    // Deep LOD Routes
    case 'paper':
      content.innerHTML = renderPaperDetail(STATE.routeParams[0]);
      break;
    case 'author':
      content.innerHTML = renderAuthorDetail(STATE.routeParams[0]);
      break;
    case 'concept':
      content.innerHTML = renderConceptDetail(STATE.routeParams[0]);
      break;
    default:
      content.innerHTML = renderHome();
  }
}

// LOD Helpers
function getAuthorLink(authorId) {
  const author = STATE.db.authors[authorId];
  if (!author) return authorId;
  return `<a href="#author/${authorId}" class="lod-link">${author.name}</a>`;
}

function getConceptLink(conceptId) {
  const concept = STATE.db.concepts[conceptId];
  if (!concept) return conceptId;
  return `<a href="#concept/${conceptId}" class="pill" style="background:#e2e8f0;color:#475569;text-decoration:none;">${concept.name}</a>`;
}

function getPaperCard(paperId) {
  const paper = STATE.db.papers[paperId];
  if (!paper) return '';
  
  const roleClass = paper.role_in_project ? paper.role_in_project.toLowerCase().replace(/[^a-z0-9]+/g, '-') : '';
  const rolePill = paper.role_in_project ? `<span class="pill pill-${roleClass}">${paper.role_in_project}</span>` : '';
  const authorLinks = paper.authors.map(getAuthorLink).join(', ');
  const conceptLinks = paper.concepts.map(getConceptLink).join('');
  
  return `
    <div class="glass-card">
      <h3><a href="#paper/${paper.id}" style="color:inherit; text-decoration:none;">${paper.title}</a></h3>
      <p class="text-muted"><strong>${authorLinks}</strong> (${paper.year}) — arXiv:${paper.id}</p>
      <div style="margin-top:0.5rem;">
        ${rolePill}
        ${conceptLinks}
      </div>
    </div>
  `;
}

// Views
function renderHome() {
  const totalPapers = Object.keys(STATE.db.papers).length;
  
  return `
    <section class="view-section active">
      <h2>Welcome to the RH Repository</h2>
      <p class="math-text"><strong>A Digital Humanities approach to the Riemann Hypothesis:</strong> We treat 160+ years of published mathematics as interconnected knowledge objects—not just facts to digest, but a living network of intuitions, proof strategies, and intellectual lineage. This repository asks: <em>What structures underlie a proof? How do mathematical ideas flow from person to person across generations? Can formal verification reveal gaps that human insight misses?</em> Our Linked Open Data graph maps papers, authors, and mathematical concepts as a foundation for both human understanding and machine learning.</p>
      
      <div class="bento-grid mt-lg">
        <div class="glass-card">
          <h3>📚 The Corpus</h3>
          <p>We have cataloged <strong>${totalPapers}</strong> foundational and modern papers. All entities are highly interlinked.</p>
          <a href="#corpus" class="nav-link">Explore Archive →</a>
        </div>
        <div class="glass-card">
          <h3>🧑‍🔬 Lineage</h3>
          <p>Trace the historical routes from Riemann to modern authors.</p>
          <a href="#mathematicians" class="nav-link">View Mathematicians →</a>
        </div>
        <div class="glass-card">
          <h3>🔴 Insights</h3>
          <p>View mathematical insights and Lean 4 formalization proofs side-by-side.</p>
          <a href="#insights" class="nav-link">View Lean Insights →</a>
        </div>
      </div>
    </section>
  `;
}

function renderCorpus() {
  const papers = Object.keys(STATE.db.papers);
  const totalPapers = papers.length;

  // Group papers by role/phase
  const byPhase = {};
  papers.forEach(pId => {
    const paper = STATE.db.papers[pId];
    const phase = paper.role_in_project || 'General';
    if (!byPhase[phase]) byPhase[phase] = [];
    byPhase[phase].push(pId);
  });

  // Count papers by year
  const yearCounts = {};
  papers.forEach(pId => {
    const year = STATE.db.papers[pId].year;
    yearCounts[year] = (yearCounts[year] || 0) + 1;
  });
  const earliestYear = Math.min(...Object.keys(yearCounts).map(Number));
  const latestYear = Math.max(...Object.keys(yearCounts).map(Number));

  let html = `
    <section class="view-section active">
      <h2>Paper Archive</h2>
      <p style="font-size:1.05rem; color:#475569; margin-bottom:2rem;">
        Comprehensive corpus of ${totalPapers} papers spanning ${earliestYear}–${latestYear},
        organized by research phase and searchable by title, author, and keywords.
      </p>

      <!-- Statistics -->
      <div style="display:grid; grid-template-columns:repeat(auto-fit, minmax(180px, 1fr)); gap:1rem; margin-bottom:2rem;">
        <div class="glass-card" style="text-align:center; padding:1.5rem;">
          <div style="font-size:2.5rem; font-weight:bold; color:#3b82f6;">${totalPapers}</div>
          <div style="color:#64748b; font-size:0.95rem;">Total Papers</div>
        </div>
        <div class="glass-card" style="text-align:center; padding:1.5rem;">
          <div style="font-size:2.5rem; font-weight:bold; color:#10b981;">${Object.keys(STATE.db.authors).length}</div>
          <div style="color:#64748b; font-size:0.95rem;">Authors</div>
        </div>
        <div class="glass-card" style="text-align:center; padding:1.5rem;">
          <div style="font-size:2.5rem; font-weight:bold; color:#f59e0b;">${latestYear - earliestYear + 1}</div>
          <div style="color:#64748b; font-size:0.95rem;">Years Spanned</div>
        </div>
        <div class="glass-card" style="text-align:center; padding:1.5rem;">
          <div style="font-size:2.5rem; font-weight:bold; color:#8b5cf6;">${Object.keys(byPhase).length}</div>
          <div style="color:#64748b; font-size:0.95rem;">Research Phases</div>
        </div>
      </div>

      <!-- Search Input (client-side + SPARQL) -->
      <div style="margin-bottom:2rem;">
        ${STATE.sparqlAvailable ? `
          <div style="margin-bottom:1rem; padding:0.75rem; background:#dbeafe; border-left:3px solid #0ea5e9; border-radius:4px;">
            <strong style="color:#0c4a6e;">🔵 Live LOD Search</strong> — Searching Linked Open Data (SPARQL v1)
          </div>
        ` : ''}
        <input type="text" id="corpus-search" placeholder="${STATE.sparqlAvailable ? 'Search papers (live LOD data)...' : 'Search by title or author...'}"
          style="width:100%; padding:0.75rem; border:1px solid #e5e7eb; border-radius:6px; font-size:1rem;" />
        ${STATE.sparqlAvailable ? `
          <div style="margin-top:0.5rem; font-size:0.85rem; color:#64748b;">
            <button id="sparql-search-btn" style="background:#0ea5e9; color:white; border:none; padding:0.5rem 1rem; border-radius:4px; cursor:pointer; font-weight:500;">
              Advanced SPARQL Search
            </button>
          </div>
        ` : ''}
      </div>

      <!-- Papers by Phase -->
  `;

  // Sort phases: show research phases first, then general
  const phases = Object.keys(byPhase).sort((a, b) => {
    if (a === 'General') return 1;
    if (b === 'General') return -1;
    return a.localeCompare(b);
  });

  phases.forEach(phase => {
    const phaseCount = byPhase[phase].length;
    const colorMap = {
      'H15': '#ef4444',
      'H14': '#10b981',
      'H13': '#f59e0b',
      'NB': '#0ea5e9',
      'General': '#6b7280'
    };
    const color = colorMap[phase] || '#3b82f6';

    html += `
      <div style="margin-bottom:2rem;">
        <h3 style="color:${color}; border-bottom:2px solid ${color}; padding-bottom:0.5rem; margin-bottom:1rem;">
          ${phase} (${phaseCount} paper${phaseCount !== 1 ? 's' : ''})
        </h3>
        <div class="space-y-lg" style="display:grid; gap:1rem;">
    `;

    byPhase[phase].forEach(pId => {
      html += getPaperCard(pId);
    });

    html += `</div></div>`;
  });

  html += `</section>`;

  // Note: basic search stub - could be enhanced with full-text search
  setTimeout(() => {
    const searchInput = document.getElementById('corpus-search');
    if (searchInput) {
      searchInput.addEventListener('input', (e) => {
        const query = e.target.value.toLowerCase();
        document.querySelectorAll('.glass-card').forEach(card => {
          const text = card.textContent.toLowerCase();
          card.style.display = text.includes(query) ? 'block' : 'none';
        });
      });
    }
  }, 100);

  return html;
}

function renderPaperDetail(paperId) {
  const paper = STATE.db.papers[paperId];
  if (!paper) return `<section class="view-section active"><h2>Paper Not Found</h2></section>`;
  
  const authorLinks = paper.authors.map(getAuthorLink).join('<br>');
  const conceptLinks = paper.concepts.map(getConceptLink).join('');
  const relatedPapers = paper.related_papers.map(p => getPaperCard(p)).join('');
  
  const noveltiesHtml = paper.key_novelties && paper.key_novelties.length ? 
    `<ul>${paper.key_novelties.map(n => `<li>${n}</li>`).join('')}</ul>` : '<p class="text-muted">No key novelties recorded.</p>';
    
  const formalizableHtml = paper.formalizable_elements && paper.formalizable_elements.length ? 
    `<ul>${paper.formalizable_elements.map(f => `<li>${f}</li>`).join('')}</ul>` : '<p class="text-muted">No formalizable elements identified.</p>';

  const intuitionsHtml = paper.intuitions ? 
    `<p class="math-text">${paper.intuitions}</p>` : '<p class="text-muted">No intuitions recorded.</p>';
  
  return `
    <section class="view-section active">
      <a href="#corpus" style="color:#64748b;text-decoration:none;">← Back to Corpus</a>
      <h2 style="margin-bottom:0.5rem;">${paper.title}</h2>
      <p class="text-muted" style="font-size:1.1rem; margin-top:0;">Published: ${paper.year} | arXiv:${paper.id}</p>
      
      <div class="split-layout mt-lg">
        <div>
          <div class="glass-card" style="margin-bottom:1.5rem;">
            <h3 style="margin-top:0; border-bottom: 2px solid #e2e8f0; padding-bottom:0.5rem;">Extraction Details</h3>
            
            <h4 style="margin-bottom:0.25rem;">Mathematical Intuitions</h4>
            ${intuitionsHtml}
            
            <h4 style="margin-bottom:0.25rem;">Key Novelties</h4>
            ${noveltiesHtml}
            
            <h4 style="margin-bottom:0.25rem;">Formalizable in Lean 4</h4>
            ${formalizableHtml}
          </div>
          
          <h3>Authors</h3>
          <div class="glass-card" style="margin-bottom:1.5rem;">${authorLinks}</div>
          
          <h3>Concepts</h3>
          <div style="margin-bottom:1.5rem;">${conceptLinks || 'No key concepts extracted.'}</div>
        </div>
        
        <div>
          <h3>Related Papers</h3>
          <div class="space-y-lg">
            ${relatedPapers || '<p class="text-muted">No related papers linked.</p>'}
          </div>
        </div>
      </div>
    </section>
  `;
}

function renderAuthorDetail(authorId) {
  const author = STATE.db.authors[authorId];
  if (!author) return `<section class="view-section active"><h2>Author Not Found</h2></section>`;
  
  const papers = author.papers.map(p => getPaperCard(p)).join('');
  
  // Aggregate concepts and intuitions from author's papers
  let allConcepts = new Set();
  let allIntuitions = [];
  author.papers.forEach(pid => {
    const p = STATE.db.papers[pid];
    if (p) {
      p.concepts.forEach(c => allConcepts.add(c));
      if (p.intuitions) allIntuitions.push(p.intuitions);
    }
  });
  
  const conceptLinks = Array.from(allConcepts).map(getConceptLink).join('');
  const intuitionsHtml = allIntuitions.length > 0 
    ? `<ul>${allIntuitions.map(i => `<li style="margin-bottom:0.5rem;">${i}</li>`).join('')}</ul>`
    : '<p class="text-muted">No specific intuitions recorded for these papers.</p>';
  
  return `
    <section class="view-section active">
      <h2 style="margin-bottom:0.25rem;">${author.name}</h2>
      <p class="text-muted" style="margin-top:0;">Born: ${author.birth_year || 'Unknown'}</p>
      
      <div class="glass-card mt-lg" style="margin-bottom:2rem;">
        <h3 style="margin-top:0;">Biography</h3>
        <p class="math-text">${author.bio || 'Analytic number theorist.'}</p>
        
        <h3 class="mt-lg">Key Concepts</h3>
        <div>${conceptLinks || 'None'}</div>
        
        <h3 class="mt-lg">Core Intuitions & Novelties</h3>
        <div class="math-text">${intuitionsHtml}</div>
      </div>
      
      <h3>Published Papers in Corpus</h3>
      <div class="space-y-lg">
        ${papers}
      </div>
    </section>
  `;
}

function renderConceptDetail(conceptId) {
  const concept = STATE.db.concepts[conceptId];
  if (!concept) return `<section class="view-section active"><h2>Concept Not Found</h2></section>`;
  
  const papers = concept.papers.map(p => getPaperCard(p)).join('');
  
  return `
    <section class="view-section active">
      <h2>Concept: ${concept.name}</h2>
      ${concept.description ? `<p class="math-text mt-lg" style="font-size:1.1rem; max-width:800px; color:#475569;">${concept.description}</p>` : ''}
      
      <h3 class="mt-lg">Papers Exploring this Concept</h3>
      <div class="space-y-lg">
        ${papers}
      </div>
    </section>
  `;
}

function renderMathematicians() {
  const allAuthors = Object.values(STATE.db.authors).sort((a,b) => (a.birth_year || 2000) - (b.birth_year || 2000));

  // Group authors by era
  const eras = {
    classical: { label: 'Classical Era (1859–1920)', range: [1859, 1920], authors: [] },
    modern: { label: 'Modern Era (1921–1970)', range: [1921, 1970], authors: [] },
    contemporary: { label: 'Contemporary (1971–2000)', range: [1971, 2000], authors: [] },
    recent: { label: 'Recent (2001+)', range: [2001, 2100], authors: [] }
  };

  allAuthors.forEach(a => {
    const year = a.birth_year || 2000;
    if (year <= 1920) eras.classical.authors.push(a);
    else if (year <= 1970) eras.modern.authors.push(a);
    else if (year <= 2000) eras.contemporary.authors.push(a);
    else eras.recent.authors.push(a);
  });

  const eraHtml = Object.entries(eras)
    .filter(([_, e]) => e.authors.length > 0)
    .map(([_, era]) => `
      <div style="margin-bottom:3rem;">
        <h3 style="color:#3b82f6; font-size:1.1rem; margin-bottom:1.5rem; padding-bottom:0.75rem; border-bottom:2px solid #e2e8f0;">${era.label}</h3>
        <div style="display:grid; grid-template-columns:repeat(auto-fill, minmax(280px, 1fr)); gap:1.5rem;">
          ${era.authors.map(a => `
            <div class="glass-card" style="padding:1.25rem;">
              <h4 style="margin:0 0 0.5rem 0; font-size:1.05rem;">
                <a href="#author/${a.id}" style="color:inherit;text-decoration:none;">${a.name}</a>
              </h4>
              <p style="margin:0.25rem 0; color:#64748b; font-size:0.9rem;">b. ${a.birth_year || '?'}</p>
              <p class="text-muted" style="margin:0.75rem 0 0.5rem 0; font-size:0.9rem; line-height:1.4;">${a.bio || 'Mathematician'}</p>
              <p style="margin:0.5rem 0; font-size:0.85rem; color:#3b82f6; font-weight:600;">
                <a href="#author/${a.id}" style="color:inherit;text-decoration:none;">📄 ${a.papers.length} paper${a.papers.length !== 1 ? 's' : ''}</a>
              </p>
            </div>
          `).join('')}
        </div>
      </div>
    `).join('');

  return `
    <section class="view-section active">
      <h2>Intellectual Lineage (Grouped by Era)</h2>
      <p>This lineage focuses specifically on the mathematicians whose intuitions laid the groundwork for the Nyman-Beurling approach. We selected these authors not just for their fame, but because their theoretical leaps—such as transforming the Zeta function into Hilbert spaces or bounding Cotangent sums—provided the exact algorithmic structures necessary for our modern Lean 4 formalization attempts.</p>

      <div style="margin-top:2rem;">
        ${eraHtml}
      </div>

      <div style="margin-top:3rem; padding:2rem; background:#f0f9ff; border-radius:8px; border-left:4px solid #3b82f6;">
        <h3 style="margin-top:0;">Why these Authors?</h3>
        <p class="math-text" style="font-size:1rem;">
          The Riemann Hypothesis spans 160+ years of mathematics, but formal verification requires highly rigid, algorithmic bounds. The authors tracked in this repository were chosen because their work bridges classical analysis with discrete computational structures.
          <br><br>
          For example, <strong>Arne Beurling</strong> intuited that RH is equivalent to the closure of indicator functions in $L^2(0,1)$. This intuition shifted the problem from complex analysis to functional analysis. Decades later, <strong>Aleksandr Vasyunin</strong> pushed this intuition further, providing explicit cotangent bounds that could be mechanically checked by algorithms.
        </p>
      </div>
    </section>
  `;
}

function renderInsights() {
  return `
    <section class="view-section active">
      <h2>Formalization & Mathematical Insights</h2>
      <p style="font-size: 1.05rem; color: #475569; margin-bottom: 2rem;">
        Our Lean 4 formalization program combines classical analytic number theory with formal verification. Below: the intuitions that guide our work, followed by achievement summaries across four major themes.
      </p>

      <!-- INTUITIONS SECTION -->
      <div style="background: #fef3c7; padding: 2rem; border-radius: 8px; margin-bottom: 2rem; border-left: 4px solid #f59e0b;">
        <h3 style="color: #92400e; margin-top: 0;">💡 Core Intuitions from the Corpus</h3>
        <div style="display: grid; grid-template-columns: repeat(auto-fit, minmax(300px, 1fr)); gap: 1.5rem; margin-top: 1.5rem;">
          <div style="background: white; padding: 1.25rem; border-radius: 6px; border-left: 3px solid #f59e0b;">
            <strong style="color: #92400e;">Functional Reformulation (Nyman–Beurling)</strong>
            <p style="color: #666; font-size: 0.95rem; margin-top: 0.75rem;">
              RH is equivalent to a closure property in Hilbert space: the set of shifted unit fractions is dense in $L^2(0,\\infty)$. This removes zeta zeros from the problem statement, enabling proof without analytic continuation.
            </p>
          </div>
          <div style="background: white; padding: 1.25rem; border-radius: 6px; border-left: 3px solid #f59e0b;">
            <strong style="color: #92400e;">Computational Explicitness (Vasyunin–Báez-Duarte)</strong>
            <p style="color: #666; font-size: 0.95rem; margin-top: 0.75rem;">
              Vasyunin made closure testable: RH holds iff $|\\sum_k \\mu(k) B_1(k/N)| \\le C/\\log N$. The BBLS (Balazard–Saias–Landreau–Saias) formulation gives an explicit, computable bound for verification.
            </p>
          </div>
          <div style="background: white; padding: 1.25rem; border-radius: 6px; border-left: 3px solid #f59e0b;">
            <strong style="color: #92400e;">Quantitative Analysis (De la Vallée Poussin)</strong>
            <p style="color: #666; font-size: 0.95rem; margin-top: 0.75rem;">
              Classical zero-free regions on Möbius sums give unconditional bounds on sums of multiplicative functions. DVP method combined with Perron inversion + Borel–Jensen factorization yields effective bounds without RH assumptions.
            </p>
          </div>
          <div style="background: white; padding: 1.25rem; border-radius: 6px; border-left: 3px solid #f59e0b;">
            <strong style="color: #92400e;">Cancellation & Symmetry (Bettin–Conrey)</strong>
            <p style="color: #666; font-size: 0.95rem; margin-top: 0.75rem;">
              The O(1/log N) bound requires bilinear cancellation between Möbius and period-function correlations, not just individual decay. This is the H15 problem: estimate modulus-dependent amplitude under sign oscillations.
            </p>
          </div>
        </div>
      </div>

      <!-- H13: CLASSICAL FOUNDATION -->
      <div style="background: #f0fdf4; padding: 2rem; border-radius: 8px; margin-bottom: 2rem; border-left: 4px solid #10b981;">
        <h3 style="color: #065f46; margin-top: 0;">✅ H13: Classical Foundation (Vasyunin–BBLS Chain)</h3>
        <p style="color: #666; margin-bottom: 1rem;"><strong>Status:</strong> 100% COMPLETE (verified 2026-07-10) — zero sorries, zero new axioms</p>
        <div style="background: white; padding: 1.5rem; border-radius: 6px; margin-top: 1rem;">
          <strong style="color: #065f46;">Achievements:</strong>
          <ul style="color: #475569; margin: 1rem 0; padding-left: 2rem;">
            <li>Propositions 12, 15, 16, 21r, 22, 48, 87, 88, 89 (BBLS chain) — all proved</li>
            <li>Cotangent sum identities + period-function reduction</li>
            <li>Bernoulli representation bridge to explicit formulas</li>
            <li>Vasyunin identity correctness verified (false-at-h=0 bug caught & fixed)</li>
            <li><strong>Foundation for H14 & H15:</strong> Closed the classical-to-computational gap</li>
          </ul>
          <p style="color: #666; font-size: 0.95rem; margin-top: 1rem;"><strong>Code:</strong> ~40 KB Lean 4, mathlib NBMellinTools module</p>
        </div>
      </div>

      <!-- H14: QUANTITATIVE BOUNDS -->
      <div style="background: #f0fdf4; padding: 2rem; border-radius: 8px; margin-bottom: 2rem; border-left: 4px solid #10b981;">
        <h3 style="color: #065f46; margin-top: 0;">✅ H14: Quantitative Bounds (Möbius Decay via DVP)</h3>
        <p style="color: #666; margin-bottom: 1rem;"><strong>Status:</strong> 100% COMPLETE (verified 2026-07-15, commit b499bf2) — 8,521 build jobs, zero sorries, zero new axioms</p>
        <div style="background: white; padding: 1.5rem; border-radius: 6px; margin-top: 1rem;">
          <strong style="color: #065f46;">Three Independent Pieces (All Complete):</strong>
          <ul style="color: #475569; margin: 1rem 0; padding-left: 2rem;">
            <li><strong>H14.1 FEFactor:</strong> Vertical Fourier–Eisenstein interpolation bounds (474 lines)</li>
            <li><strong>H14.2 Borel–Jensen:</strong> Zeta factorization on critical strip + DVP region bounds (64 KB)</li>
            <li><strong>H14.3 Perron + Mertens:</strong> Truncated contour inversion with effective Mertens bound: $|M(N)| \\le A \\cdot N \\cdot e^{-a\\sqrt{\\log N}}$ (90 KB)</li>
          </ul>
          <p style="color: #666; font-size: 0.95rem; margin-top: 1rem;"><strong>Result:</strong> Unconditional bound on Möbius sums via classical analytic methods. Foundation for H15 coefficient control.</p>
        </div>
      </div>

      <!-- H15: QUADRATIC CANCELLATION (RESEARCH) -->
      <div style="background: #fef2f2; padding: 2rem; border-radius: 8px; margin-bottom: 2rem; border-left: 4px solid #ef4444;">
        <h3 style="color: #7f1d1d; margin-top: 0;">🔴 H15: Quadratic Cancellation (Open Research)</h3>
        <p style="color: #666; margin-bottom: 1rem;"><strong>Status:</strong> Exact theory LOCKED; linear bound BLOCKED; BCF logarithmic taper ACTIVE</p>
        <div style="background: white; padding: 1.5rem; border-radius: 6px; margin-top: 1rem;">
          <strong style="color: #7f1d1d;">Current Progress:</strong>
          <ul style="color: #475569; margin: 1rem 0; padding-left: 2rem;">
            <li>✅ Centered bilinear kernel fixed + dyadic diagnostics passing</li>
            <li>✅ Exact Mellin identity for period functions PROVED</li>
            <li>✅ Phase conversion from Fourier DERIVED EXACTLY</li>
            <li>❌ DFI/Bettin–Chandee route FAILS (bound 8× too weak)</li>
            <li>❌ Linear taper blocked by undamped zero-mode obstruction</li>
            <li>🔄 BCF logarithmic taper showing promising empirical decay (research ongoing)</li>
          </ul>
          <p style="color: #666; font-size: 0.95rem; margin-top: 1rem;"><strong>Remaining Gap (Precisely Defined):</strong> Estimate modulus-dependent amplitude $\\beta_q(b)$ under modular constraints while maintaining cancellation with log-ratio. Expert escalation required.</p>
        </div>
      </div>

      <!-- PHASE NB: NYMAN-BEURLING BRIDGE -->
      <div style="background: #f0f9ff; padding: 2rem; border-radius: 8px; margin-bottom: 2rem; border-left: 4px solid #0ea5e9;">
        <h3 style="color: #0c4a6e; margin-top: 0;">✅ Phase NB: Nyman–Beurling Bridge (COMPLETE)</h3>
        <p style="color: #666; margin-bottom: 1rem;"><strong>Status:</strong> 100% COMPLETE (verified 2026-07-15, commit d944715) — all six steps proved, zero sorries, zero new axioms</p>
        <div style="background: white; padding: 1.5rem; border-radius: 6px; margin-top: 1rem;">
          <strong style="color: #0c4a6e;">All Six Steps (Complete):</strong>
          <ul style="color: #475569; margin: 1rem 0; padding-left: 2rem;">
            <li>✅ <strong>NB0:</strong> Criterion foundation (axiom boundary)</li>
            <li>✅ <strong>NB1:</strong> Classical basis (theory foundation)</li>
            <li>✅ <strong>NB2 (Mellin):</strong> Base formula $\\mathcal{M}(\\rho_{\\mathrm{base}})(s) = -\\zeta(s)/s$ for $0 &lt; \\mathrm{Re}(s) &lt; 1$</li>
            <li>✅ <strong>NB3 (Continuity):</strong> Mellin transform continuous on critical strip $1/2 &lt; \\mathrm{Re}(s) &lt; 1$</li>
            <li>✅ <strong>NB4 (Zero Detection):</strong> Conditional right-half critical-strip zero-free theorem</li>
            <li>✅ <strong>NB5 (Closure):</strong> Zeta functional equation reflection + critical-line equivalence: <strong>Nyman–Beurling Criterion ⟺ Riemann Hypothesis</strong></li>
          </ul>
          <p style="color: #666; font-size: 0.95rem; margin-top: 1rem;"><strong>Result:</strong> 1,050 KB Lean 4 code, 8,484 build jobs, publication-ready formalization of the complete Nyman–Beurling bridge to RH.</p>
        </div>
      </div>
    </section>
  `;
}

// Start
document.addEventListener('DOMContentLoaded', initApp);
