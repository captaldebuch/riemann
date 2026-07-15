/**
 * DH Repository SPA Application Logic (LOD Edition)
 */

const STATE = {
  db: null,
  currentRoute: 'home',
  routeParams: null,
  isLoading: true
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
  
  let html = `
    <section class="view-section active">
      <h2>Paper Archive</h2>
      <p>All structured knowledge artifacts currently indexed in the repository.</p>
      <div class="space-y-lg">
  `;
  
  papers.forEach(pId => {
    html += getPaperCard(pId);
  });
  
  html += `</div></section>`;
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
  
  let listHtml = '<div style="position:relative; padding-left:1.5rem; border-left:2px solid #e2e8f0; margin-top:2rem;">';
  listHtml += allAuthors.map(a => `
    <div style="position:relative; margin-bottom:2rem;">
      <div style="position:absolute; left:-1.8rem; top:0.5rem; width:10px; height:10px; background:#3b82f6; border-radius:50%;"></div>
      <div class="glass-card">
        <h3 style="margin:0; font-size:1.25rem;">
          <a href="#author/${a.id}" style="color:inherit;text-decoration:none;">${a.name}</a>
          <span style="font-size:0.9rem; color:#64748b; margin-left:0.5rem;">(b. ${a.birth_year || 'Unknown'})</span>
        </h3>
        <p class="text-muted" style="margin:0.5rem 0; font-size:0.95rem;">${a.bio || 'Analytic Number Theorist'}</p>
        <p class="text-small" style="margin:0; font-weight:600;"><a href="#author/${a.id}">${a.papers.length} paper(s) in corpus →</a></p>
      </div>
    </div>
  `).join('');
  listHtml += '</div>';

  return `
    <section class="view-section active">
      <h2>Intellectual Lineage (Chronology)</h2>
      <p>This lineage focuses specifically on the mathematicians whose intuitions laid the groundwork for the Nyman-Beurling approach. We selected these authors not just for their fame, but because their theoretical leaps—such as transforming the Zeta function into Hilbert spaces or bounding Cotangent sums—provided the exact algorithmic structures necessary for our modern Lean 4 formalization attempts.</p>
      <div class="split-layout mt-lg">
        <div>
          ${listHtml}
        </div>
        
        <div>
          <div class="glass-card" style="margin-bottom:2rem;">
            <h2 style="margin-top:0;">Why these Authors?</h2>
            <p class="math-text" style="font-size:1.05rem;">
              The Riemann Hypothesis spans 160+ years of mathematics, but formal verification requires highly rigid, algorithmic bounds. The authors tracked in this repository were chosen because their work bridges classical analysis with discrete computational structures.
              <br><br>
              For example, <strong>Arne Beurling</strong> intuited that RH is equivalent to the closure of indicator functions in $L^2(0,1)$. This intuition shifted the problem from complex analysis to functional analysis. Decades later, <strong>Aleksandr Vasyunin</strong> pushed this intuition further, providing explicit cotangent bounds that could be mechanically checked by algorithms.
            </p>
          </div>
          <div class="glass-card">
            <h2 style="margin-top:0;">Aleksandr Vasyunin</h2>
            <p class="math-text">Proved the Vasyunin cotangent identity, which expresses the Nyman-Beurling problem in terms of weighted sums of cotangent functions.</p>
            <a href="#author/author:aleksandr-vasyunin" class="pill" style="background:#3b82f6;color:white;text-decoration:none;">View Author Profile</a>
          </div>
        </div>
      </div>
    </section>
  `;
}

function renderInsights() {
  return `
    <section class="view-section active">
      <h2>Formalization & Mathematical Insights</h2>
      <p>This split view highlights the reality of modern theorem proving: the friction between classical analytic number theory and rigid formal verification.</p>
      
      <div class="insight-viewer mt-lg">
        <div class="insight-pane">
          <h3>Lean 4 and its Limits</h3>
          <span class="pill pill-mobius-cancellation">Critical Issues</span>
          <p class="math-text mt-lg">
            Our formalization attempts revealed deep structural limits. The core problem, the <strong>Möbius-Sawtooth Bounds</strong>, relies on an unproven conjecture.
            <br><br>
            <strong>Numerical Limits:</strong> The constant $C=5$ fails on 56% of test cases. Actual bounds are completely unknown.<br><br>
            <strong>Mathematical Limits:</strong> Key references (like Bettin-Conrey-Farmer) implicitly <em>assume</em> the Riemann Hypothesis, creating a circular proof if used to derive it.<br><br>
            <strong>Lean Limits:</strong> The formal gatekeeper rejects these false steps. Definitions remain as stubs (e.g. Möbius always 0 for $n > 1$) because the foundational theorems lack rigorous classical justification.
          </p>
          <p class="text-small text-muted">Conclusion: This is research scaffolding identifying missing mathematics, not a complete proof.</p>
        </div>
        
        <div class="code-pane">
          <h3>H15_RouteA.lean (Formalization Stubs)</h3>
          <pre><code>
-- The Lean gatekeeper prevents false proofs.
-- The following are axioms, not proven theorems:

axiom bettin_conrey_farmer : 
  -- Cannot be used to prove RH because it assumes RH
  False 

axiom mobius_bound (N : ℕ) :
  -- Fails numerically for 56% of test cases
  |∑_k μ(k)(1 - k/(N+1))B₁(A/k)| ≤ 5/Real.log (N+2)^2

theorem mobius_bound_implies_rh : RiemannHypothesis := by
  sorry -- Definitions are stubs
          </code></pre>
        </div>
      </div>
    </section>
  `;
}

// Start
document.addEventListener('DOMContentLoaded', initApp);
