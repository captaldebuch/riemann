import os

# Fix app.js
app_js_path = 'doc/html/js/app.js'
with open(app_js_path, 'r', encoding='utf-8') as f:
    app_js = f.read()

# 1. Remove H15 zip link
app_js = app_js.replace('<a href="./lean/H15_structure.zip" target="_blank" style="display:inline-block; padding:0.5rem 1rem; background:#f1f5f9; color:#334155; border:1px solid #cbd5e1; border-radius:4px; text-decoration:none;">📂 Browse H15 Phases 1–7</a>', '')

# 2. Fix Milestone comment
app_js = app_js.replace('<!-- MILESTONE: 94% RH FORMALIZATION -->', '<!-- MILESTONE: RH FORMALIZATION -->')

# 3. Remove "This brings total RH formalization to ~94%."
app_js = app_js.replace(' This brings total RH formalization to ~94%.', '')

# 4. Remove paragraph about 27% / 94%
app_js = app_js.replace('<p>This formalization represents ~27% additional RH coverage, bringing the total to 94% when combined with H13, H14, and Phase NB.</p>', '')

# 5. Remove the Impact block
impact_block = """        <div style="margin-top:2rem; padding:1rem; background:#e8f4f8; border-radius:4px; font-size:0.9rem;">
          <strong>Impact:</strong> H15 conditional formalization brings total RH proof coverage to 94%, leaving only 6% (expert algebraic routes) unformalized.
        </div>"""
app_js = app_js.replace(impact_block, '')

# Add an extra check for the 94% string just in case
if '94%' in app_js:
    print("Warning: '94%' still found in app.js after replacements!")
else:
    print("All '94%' references removed from app.js.")

with open(app_js_path, 'w', encoding='utf-8') as f:
    f.write(app_js)


# Fix corpus_archive.html
corpus_path = 'doc/html/corpus_archive.html'
if os.path.exists(corpus_path):
    with open(corpus_path, 'r', encoding='utf-8') as f:
        corpus_html = f.read()
    
    corpus_html = corpus_html.replace('kg_math/0306251.html', 'kg_math_0306251.html')
    corpus_html = corpus_html.replace('kg_math/9912107.html', 'kg_math_9912107.html')
    
    with open(corpus_path, 'w', encoding='utf-8') as f:
        f.write(corpus_html)
    print("Fixed corpus_archive.html links.")
else:
    print("corpus_archive.html not found.")

