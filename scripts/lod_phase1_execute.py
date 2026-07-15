#!/usr/bin/env python3
"""
LOD Phase 1: Data Cleansing - FAST EXECUTION
Fixes what we can immediately without external API calls
Ready for Phase 2 after this step

Run: python3 scripts/lod_phase1_execute.py
"""

import json
import re
from collections import defaultdict

def infer_year_from_arxiv_id(arxiv_id: str) -> int:
    """Extract year from arXiv ID (format: YYMM.XXXXX)"""
    if not arxiv_id or len(arxiv_id) < 4:
        return None

    try:
        match = re.match(r'(\d{2})(\d{2})', arxiv_id)
        if match:
            yy = int(match.group(1))
            # heuristic: 00-30 → 2000-2030, 31-99 → 1931-1999 (pre-arXiv but use for sorting)
            if yy <= 30:
                year = 2000 + yy
            else:
                year = 1900 + yy

            # Validate reasonable range
            if 1990 <= year <= 2030:
                return year
    except:
        pass

    return None

def infer_year_from_filename(filename: str) -> int:
    """Try to extract year from PDF filename"""
    if not filename:
        return None

    # Pattern: YYMM or full year
    match = re.search(r'(\d{4})', filename)
    if match:
        year = int(match.group(1))
        if 1990 <= year <= 2030:
            return year

    # Try YYMM pattern
    match = re.search(r'(\d{2})(\d{2})', filename)
    if match:
        yy = int(match.group(1))
        if yy <= 30:
            return 2000 + yy
        elif yy >= 90:
            return 1900 + yy

    return None

def extract_arxiv_id_from_filename(filename: str) -> str:
    """Extract arXiv ID from PDF filename"""
    if not filename:
        return None

    # Pattern: YYMM.XXXXX or YYMM.XXXXXvN
    match = re.search(r'(\d{4}\.\d{5})', filename)
    if match:
        return match.group(1)

    return None

def cleanse_corpus():
    """Execute Phase 1 cleansing"""
    db = json.load(open('rh_corpus_database_complete.json'))
    articles = db.get('articles', [])

    print("=" * 70)
    print("LOD PHASE 1: DATA CLEANSING")
    print("=" * 70)
    print(f"Processing {len(articles)} articles...\n")

    stats = {
        'years_fixed': 0,
        'arxiv_ids_standardized': 0,
        'unknown_author_entries': 0,
        'generic_titles': 0,
        'invalid_years': 0,
    }

    # Process each article
    for i, article in enumerate(articles):
        if i % 20 == 0 and i > 0:
            print(f"  ✓ Processed {i}/{len(articles)} articles")

        # 1. Fix malformed years
        year = article.get('year')

        if not year or (isinstance(year, int) and (year < 1990 or year > 2030)):
            # Try to infer from arxiv_id
            inferred = infer_year_from_arxiv_id(article.get('arxiv_id', ''))

            # Fallback: infer from filename
            if not inferred:
                inferred = infer_year_from_filename(article.get('local_pdf_path', ''))

            if inferred:
                article['year'] = inferred
                stats['years_fixed'] += 1

        # 2. Standardize arXiv ID
        if not article.get('arxiv_id') or article.get('arxiv_id').startswith('9901'):
            # Try to extract from filename
            arxiv_from_file = extract_arxiv_id_from_filename(article.get('local_pdf_path', ''))
            if arxiv_from_file:
                article['arxiv_id'] = arxiv_from_file
                stats['arxiv_ids_standardized'] += 1

        # 3. Track unknown authors
        if any(au.get('name') == 'Unknown Author' for au in article.get('authors', [])):
            stats['unknown_author_entries'] += 1

        # 4. Track generic titles
        title = article.get('title', '').lower()
        if title.startswith('paper_') or 'optimal choice of dirichlet' in title:
            stats['generic_titles'] += 1

        articles[i] = article

    # Update database
    db['articles'] = articles

    # 5. Summary statistics
    print(f"\n✓ Processed {len(articles)} articles\n")
    print("=" * 70)
    print("CLEANSING SUMMARY")
    print("=" * 70)
    print(f"Years fixed:              {stats['years_fixed']}")
    print(f"ArXiv IDs standardized:   {stats['arxiv_ids_standardized']}")
    print(f"Unknown author entries:   {stats['unknown_author_entries']} (need API lookup)")
    print(f"Generic titles:           {stats['generic_titles']} (need API lookup)")

    # 6. Validation report
    print(f"\n" + "=" * 70)
    print("VALIDATION")
    print("=" * 70)

    # Check data quality
    valid_years = sum(1 for a in articles if isinstance(a.get('year'), int) and 1990 <= a['year'] <= 2030)
    has_arxiv = sum(1 for a in articles if a.get('arxiv_id') and not a['arxiv_id'].startswith('9901'))
    has_title = sum(1 for a in articles if a.get('title') and not a['title'].lower().startswith('paper_'))
    has_authors = sum(1 for a in articles if a.get('authors') and len(a['authors']) > 0)

    print(f"Valid years (1990-2030):  {valid_years}/{len(articles)} ({100*valid_years//len(articles)}%)")
    print(f"Real arXiv IDs:           {has_arxiv}/{len(articles)} ({100*has_arxiv//len(articles)}%)")
    print(f"Real titles:              {has_title}/{len(articles)} ({100*has_title//len(articles)}%)")
    print(f"Has authors:              {has_authors}/{len(articles)} ({100*has_authors//len(articles)}%)")

    # 7. Save cleaned version
    output_file = 'rh_corpus_database_cleaned.json'
    with open(output_file, 'w') as f:
        json.dump(db, f, indent=2)

    print(f"\n✓ Cleaned database saved: {output_file}")
    print(f"\nNext steps:")
    print(f"1. Manual review of {stats['unknown_author_entries']} unknown authors")
    print(f"2. Manual review of {stats['generic_titles']} generic titles")
    print(f"3. Phase 2: Ontology Mapping (BIBO, FOAF, DCTERMS, CITO, SKOS)")

    return db

if __name__ == '__main__':
    cleanse_corpus()
