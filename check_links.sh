#!/bin/bash
urls=(
  "https://en.wikipedia.org/wiki/Riemann_hypothesis"
  "https://www.claymath.org/millennium/riemann-hypothesis/"
  "https://arxiv.org/abs/1509.05128"
  "https://www.ams.org/journals/notices/202211/rnoti-p1800.pdf"
  "https://www.cs.cmu.edu/~jw/papers/mizar-survey.pdf"
  "https://www.idsia.ch/~juergen/ai-godel.html"
  "https://www.hastac.org/"
  "https://www.neh.gov/divisions/odh"
  "https://dhcommons.org/"
  "https://www.w3.org/TR/rdf11-concepts/"
  "https://www.w3.org/TR/sparql11-query/"
  "https://dbpedia.org/"
)
for url in "${urls[@]}"; do
  status=$(curl -sL -o /dev/null -w "%{http_code}" -m 10 "$url")
  echo "$status $url"
done
