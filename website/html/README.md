# RH Formalization Static Website

A self-contained, responsive HTML website documenting the Riemann Hypothesis formalization project via the Nyman–Beurling criterion.

## Features

- **Static HTML** — No dependencies, CDN, or external scripts
- **Semantic HTML5** — Accessible, machine-readable structure
- **Mobile-first responsive CSS** — Flexbox/grid layout, media queries
- **Minimal vanilla JS** — Navigation and smooth scrolling only
- **Self-hosted assets** — All fonts, styles, scripts embedded

## Files

```
html/
├── index.html          ← Home page: quick overview
├── about.html          ← Project vision and philosophy
├── status.html         ← Current metrics and blockers (most detailed)
├── papers.html         ← Literature guide (4 core papers)
├── research.html       ← H15 research programme (open problem + 3 routes)
├── roadmap.html        ← Complete timeline to RH (next steps)
├── README.md           ← This file
├── css/
│   └── style.css       ← Single responsive stylesheet (mobile-first)
└── js/
    └── main.js         ← Minimal enhancement (nav, smooth scroll)
```

## How to Use

1. **Open locally:** Open `index.html` in any browser (no server needed)
2. **Host anywhere:** Copy `html/` folder to any static host (GitHub Pages, Netlify, Vercel)
3. **Update content:** Edit any `.html` file directly; no build process

## How to Update

### Quick Updates
- Edit HTML files directly (e.g., `status.html`)
- No build step needed
- Changes appear immediately when you reload

### Adding a New Page
1. Create a new `.html` file (copy structure from existing pages)
2. Add link to it in the `<nav>` block of all pages:
   ```html
   <li><a href="new-page.html">New Page</a></li>
   ```
3. Use semantic HTML: `<header>`, `<nav>`, `<main>`, `<article>`, `<footer>`

### Styling
- Edit `css/style.css` (single file)
- Uses CSS custom properties (`:root` variables)
- Mobile-first: add media queries for larger screens

## Design Decisions

### Why static HTML?
- No dependencies (works anywhere)
- Fast (minimal JS)
- Accessible (semantic HTML)
- Easy to maintain (plain text files)
- Works "on a USB stick"

### CSS Approach
- **Mobile-first:** Start with mobile layout, enhance for larger screens
- **Relative units:** Uses rem/em/%, not fixed px widths
- **Flexbox/Grid:** Modern layout without CSS frameworks
- **Custom properties:** Easy to adjust colors, spacing globally

### JavaScript Approach
- **Progressive enhancement:** JS adds interactivity, not content
- **Minimal:** Only for navigation active state, smooth scroll, code copy
- **No dependencies:** Pure vanilla JS, works everywhere

## Accessibility

- Semantic HTML (`<header>`, `<nav>`, `<main>`, `<article>`)
- Proper heading hierarchy (h1 → h3)
- Alt text on images (if images added)
- Good contrast (WCAG AA compliant colors)
- Keyboard navigation supported

## Performance

- Single CSS file (~8KB)
- Single JS file (~0.5KB)
- No external requests (fonts inline-able if needed)
- No layout shifts (CSS loads before content)
- Fast Core Web Vitals

## Browser Support

Works on all modern browsers:
- Chrome/Edge 90+
- Firefox 88+
- Safari 14+
- Mobile browsers (iOS Safari, Chrome Mobile)

## Customization

### Colors
Edit `:root` variables in `css/style.css`:
```css
:root {
  --color-primary: #1a5490;
  --color-secondary: #0d3b66;
  --color-accent: #ee964b;
  /* ... */
}
```

### Fonts
Current: System fonts (no external dependencies). To change, edit `--font-sans` and `--font-mono` in CSS.

### Spacing
Edit `--spacing-unit` in CSS:
```css
:root {
  --spacing-unit: 0.5rem;  /* Adjust all spacing globally */
}
```

## Deployment

### GitHub Pages
1. Copy `html/` folder to your repo
2. Enable GitHub Pages in Settings
3. Point to the `html/` directory
4. Done (automatic updates on git push)

### Netlify / Vercel
1. Connect your repo
2. Set build command: (none)
3. Set publish directory: `doc/html`
4. Deploy

### Traditional Hosting
1. Upload `html/` folder via FTP or SSH
2. Point domain to the folder
3. Done

## Notes

- **No Jekyll/Hugo/build step needed** — Deploy HTML directly
- **SEO-friendly** — Semantic HTML, meta tags, structured content
- **Print-friendly** — CSS includes print media queries
- **Emoji-safe** — HTML charset=utf-8 handles all emoji and Unicode

## Version History

- **2026-07-14** — Initial release: 6 pages, responsive CSS, minimal JS
- **Updates:** Edit files directly; no version numbering needed for static files

---

**This website documents research scaffolding. It is honest about what's proved, what's open, and what's needed.**
