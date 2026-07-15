import os

html_dir = "/Users/xavierfresquet/Documents/Musicologie/CAPTAL-LAB/4-MISC/math/riemann/doc/html"

redirects = {
    "corpus.html": "index.html#corpus",
    "mathematicians.html": "index.html#mathematicians",
    "knowledge-explorer.html": "index.html#graph",
    "intro.html": "index.html#home",
    "intuitions.html": "index.html#insights",
    "about.html": "index.html#home",
    "papers.html": "index.html#corpus",
    "paper-analysis.html": "index.html#insights",
    "research.html": "index.html#insights",
    "roadmap.html": "index.html#home",
    "status.html": "index.html#home",
    "visualizations.html": "index.html#graph"
}

redirect_template = """<!DOCTYPE html>
<html>
<head>
    <meta charset="utf-8">
    <title>Redirecting to DH Repository...</title>
    <script>window.location.replace("{target}");</script>
</head>
<body>
    <p>Redirecting to the new Data Repository <a href="{target}">here</a>.</p>
</body>
</html>"""

for filename, target in redirects.items():
    filepath = os.path.join(html_dir, filename)
    if os.path.exists(filepath):
        with open(filepath, 'w') as f:
            f.write(redirect_template.format(target=target))

print("Redirects applied to legacy HTML files.")
