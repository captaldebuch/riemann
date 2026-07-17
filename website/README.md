# Interactive Website

A dynamic single-page application (SPA) for exploring the Riemann Hypothesis corpus, formalization progress, and technical reports.

## Quick Start

### Run Locally
```bash
cd website
python3 localhost.py
# Open http://localhost:8000 in browser
```

### Deploy to Production
```bash
# Copy to web server
cp -r html /var/www/riemann/

# Or deploy to GitHub Pages
git subtree push --prefix website/html origin gh-pages

# Or deploy to Netlify
# (Drag & drop html folder to Netlify)
```

## Features

### 📚 Corpus Explorer
- Search 78 papers by title, author, keyword
- View paper metadata and extraction details
- See related papers and concept connections
- Access PDF downloads and arXiv links

### 🧠 Intuitions & Strategies
- Interactive timeline of 160+ years of RH research
- 26 mathematician profiles with biography, contributions, papers
- Conceptual map connecting ideas across routes
- Four major approaches:
  - Classical (analytic)
  - Spectral (Hilbert-Pólya)
  - Probabilistic (Montgomery-GUE)
  - Functional (Nyman-Beurling)

### 📊 Current Efforts
- Real-time formalization status
- Phase-by-phase breakdown (H13, H14, Phase NB, H15)
- Progress indicators
- Links to Lean source code

### 📖 Technical Reports
- H13: Classical Routes formalization
- H14: Quantitative Bounds formalization
- Phase NB: Nyman-Beurling Bridge formalization
- H15: BCF Asymptotic (conditional)
- Each report: 2-page scientific paper style

### 🔗 Lean Integration
- View H15BCF proof files locally
- Direct links to GitHub source
- Syntax highlighting for Lean code

## File Structure

```
website/
├── html/                      # Static website files
│   ├── index.html            # Main HTML (SPA)
│   ├── css/
│   │   ├── design-system.css # Design tokens & resets
│   │   └── app.css           # Main styling
│   ├── js/
│   │   ├── app.js            # SPA router & pages
│   │   ├── data.js           # Embedded corpus data
│   │   └── sparql-client.js  # LOD query client (optional)
│   ├── downloads/            # Archive downloads
│   │   ├── PhaseNB_mathlib.zip
│   │   ├── H14_proofs.zip
│   │   └── H15_structure.zip
│   └── lean/                 # Local proof files (for viewing)
│       ├── H15BCF/
│       │   ├── GenusOneMajorantReduction.lean
│       │   ├── GenusOneWeierstrass.lean
│       │   ├── FinalAnalyticAssembly.lean
│       │   └── ... (all Phase 7b proofs)
│       └── view-proof.html   # Proof viewer
├── localhost.py              # Development server
└── README.md                 # This file
```

## Pages

### Home (`#home`)
- Project overview
- Key achievements
- Navigation to all sections

### Corpus & Dataset (`#corpus-dataset`)
- 78 papers organized by category
- Full-text search
- Paper detail view with:
  - Metadata (authors, year, concepts)
  - Key novelties
  - Formalizable elements
  - Related papers

### Intuitions & Strategies (`#intuitions`)
- Timeline of mathematicians (1859–2023)
- Interactive profiles for 26 key researchers
- Four RH approach routes:
  - **Analytic:** Explicit formulas, bounds (Titchmarsh, Conrey)
  - **Spectral:** Hilbert-Pólya hypothesis (Connes, Berry)
  - **Probabilistic:** Random matrices, GUE (Montgomery, Forrester)
  - **Functional:** Nyman-Beurling, Hardy spaces (Beurling, Burnol)

### Current Efforts (`#achievements`)
- **H13:** Classical identities (BBLS) — ✅ COMPLETE
- **H14:** Quantitative bounds (DVP) — ✅ COMPLETE
- **Phase NB:** Functional analysis criterion — ✅ COMPLETE
- **H15:** Conditional asymptotic (BCF) — 🔄 IN PROGRESS
  - Phases 1–7: ✅ COMPLETE
  - Phase 7b: In progress
    - Phase 7b.1: Energy-residue reduction
    - Phase 7b.2: Hadamard endpoint identities
    - Phase 7b.3: Assembly

### Technical Reports (`#technical-reports`)
- H13 + H14: Classical Routes Report
- Phase NB: Functional Analysis Report
- H15: BCF Asymptotic Report
- Each includes:
  - Abstract & authors
  - Sections list
  - Key concepts
  - View/download buttons

## Customizing the Website

### Change Metadata (Title, Description)
Edit `html/index.html`:
```html
<meta name="description" content="Your description here">
<title>Your Title</title>
```

### Change Styling
Edit `html/css/app.css` or `html/css/design-system.css`

### Add a New Page
In `html/js/app.js`, add route:
```javascript
case 'new-page':
  content.innerHTML = renderNewPage();
  break;
```

Then implement `renderNewPage()` function.

### Update Corpus Data
Replace `html/js/data.js` with new JSON from:
```bash
python3 ../notebooks/01_corpus_ingestion.ipynb
```

## Checking Links

Verify all website links work:
```bash
# From parent directory
python3 link_checker.py website/html/

# Output shows broken links (if any)
```

### Common Link Issues

**Problem:** Links to Lean files broken
**Solution:** Ensure `website/lean/H15BCF/` contains all proof files
```bash
cp -r ../proofs/NBMellinTools/H15BCF/* html/lean/H15BCF/
```

**Problem:** PDF downloads 404
**Solution:** Verify PDFs exist in `html/downloads/`
```bash
ls html/downloads/*.pdf
```

**Problem:** Images missing
**Solution:** Check image paths in CSS:
```bash
grep -r "url(" html/css/ | grep -v "fonts.googleapis"
```

## Performance Optimization

### Reduce Bundle Size
```bash
# Minify CSS
npx cssnano html/css/app.css -o html/css/app.min.css

# Minify JS (keep for readability, or use build tool)
npx terser html/js/app.js -o html/js/app.min.js
```

### Enable Caching
Add `.htaccess` for Apache:
```apache
<IfModule mod_expires.c>
  ExpiresActive On
  ExpiresByType text/html "access plus 1 hour"
  ExpiresByType text/css "access plus 1 year"
  ExpiresByType text/javascript "access plus 1 year"
</IfModule>
```

### Compress Assets
```bash
gzip -k html/css/app.css
gzip -k html/js/app.js
gzip -k html/js/data.js
```

## Accessibility

Website follows WCAG 2.1 guidelines:
- Semantic HTML (`<section>`, `<article>`, `<nav>`)
- Proper heading hierarchy (h1 → h2 → h3)
- Color contrast ratios ≥ 4.5:1 for text
- Skip navigation links
- ARIA labels where appropriate

Test with:
```bash
# Browser tools
# - Chrome DevTools > Lighthouse
# - Firefox Inspector > Accessibility panel
```

## Analytics (Optional)

To add tracking:

```html
<!-- Add to html/index.html before </body> -->
<script async src="https://www.googletagmanager.com/gtag/js?id=GA_MEASUREMENT_ID"></script>
<script>
  window.dataLayer = window.dataLayer || [];
  function gtag(){dataLayer.push(arguments);}
  gtag('js', new Date());
  gtag('config', 'GA_MEASUREMENT_ID');
</script>
```

Or use privacy-respecting alternatives:
- **Plausible.io** (GDPR-friendly)
- **Fathom Analytics** (privacy-first)
- **Matomo** (self-hosted)

## Mobile Responsiveness

Website is fully responsive:
- Mobile: < 768px width
- Tablet: 768px – 1024px
- Desktop: > 1024px

Test with:
```bash
# Browser DevTools
# - Toggle device toolbar (Ctrl+Shift+M / Cmd+Shift+M)
```

## Deployment Guides

### GitHub Pages
```bash
git subtree push --prefix website/html origin gh-pages
# Site available at: https://xavierfresquet.github.io/riemann-hypothesis/
```

### Netlify
1. Drag & drop `website/html` folder to Netlify
2. Or connect GitHub repo and auto-deploy

### Traditional Web Server
```bash
# On server:
scp -r website/html user@server:/var/www/riemann/
```

Then configure Apache/Nginx to serve `/var/www/riemann/index.html` for all routes (SPA requirement):

**Apache (.htaccess):**
```apache
<IfModule mod_rewrite.c>
  RewriteEngine On
  RewriteBase /
  RewriteRule ^index\.html$ - [L]
  RewriteCond %{REQUEST_FILENAME} !-f
  RewriteCond %{REQUEST_FILENAME} !-d
  RewriteRule . /index.html [L]
</IfModule>
```

**Nginx:**
```nginx
server {
  listen 80;
  root /var/www/riemann;
  
  location / {
    try_files $uri /index.html;
  }
}
```

## Support

- **Issues:** [GitHub Issues](https://github.com/xavierfresquet/riemann-hypothesis/issues)
- **Discussions:** [GitHub Discussions](https://github.com/xavierfresquet/riemann-hypothesis/discussions)
- **Email:** xavier.fresquet@sorbonne.ae

---

**Last updated:** July 17, 2026  
**Browser support:** Chrome, Firefox, Safari, Edge (latest versions)  
**Performance:** Lighthouse score 90+
