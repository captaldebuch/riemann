#!/usr/bin/env python3
"""
LOD Phase 1: Data Cleansing Pipeline
Resolves unknown authors, malformed years, adds DOIs, deduplicates

Run: python3 lod_phase1_cleanse.py
"""

import json
import re
import urllib.request
import urllib.error
import time
from typing import Dict, List, Optional, Tuple

# Configuration
ARXIV_API = "http://export.arxiv.org/api/query?id_list={}"
CROSSREF_API = "https://api.crossref.org/works?query={}&rows=5"
ARXIV_QUERY = "http://export.arxiv.org/api/query?search_query=all:{}&max_results=5"

class LODCleaner:
    def __init__(self, db_path: str = "rh_corpus_database_complete.json"):
        self.db_path = db_path
        self.db = json.load(open(db_path))
        self.articles = self.db.get('articles', [])
        self.stats = {
            'unknown_authors_resolved': 0,
            'years_fixed': 0,
            'dois_added': 0,
            'titles_corrected': 0,
            'errors': []
        }

    def infer_year_from_arxiv_id(self, arxiv_id: str) -> Optional[int]:
        """Extract year from arXiv ID (format: YYMM.XXXXX or arXiv:0706.XXXX)"""
        if not arxiv_id:
            return None

        # Format: YYMM.XXXXX (post-2007) or arXiv:XXXX.XXXXX
        match = re.match(r'(\d{2})(\d{2})', arxiv_id)
        if match:
            yy = int(match.group(1))
            # Heuristic: 00-06 → 2000-2006, 07-99 → 2007-2099 (arXiv launch was 1991 but common 2000s onward)
            year = (2000 + yy) if yy >= 0 and yy <= 30 else (1900 + yy)
            if year >= 1991 and year <= 2030:
                return year
        return None

    def infer_year_from_filename(self, filename: str) -> Optional[int]:
        """Try to extract year from PDF filename"""
        # Pattern: YYMM.XXXXX in filename
        match = re.search(r'(\d{4})', filename)
        if match:
            year = int(match.group(1))
            if 1800 <= year <= 2030:
                return year
        return None

    def fetch_arxiv_metadata(self, arxiv_id: str) -> Optional[Dict]:
        """Fetch paper metadata from arXiv API"""
        if not arxiv_id or len(arxiv_id) < 4:
            return None

        try:
            url = ARXIV_API.format(arxiv_id)
            with urllib.request.urlopen(url, timeout=5) as response:
                content = response.read().decode('utf-8')

                # Parse XML response (simplified)
                title_match = re.search(r'<title>([^<]+)</title>', content)
                authors = re.findall(r'<name>([^<]+)</name>', content)
                published_match = re.search(r'<published>(\d{4})-', content)

                return {
                    'title': title_match.group(1) if title_match else None,
                    'authors': authors if authors else [],
                    'year': int(published_match.group(1)) if published_match else None
                }
        except Exception as e:
            self.stats['errors'].append(f"arXiv lookup {arxiv_id}: {str(e)}")
            return None

    def fetch_crossref_doi(self, title: str, authors: List[str]) -> Optional[str]:
        """Attempt to find DOI via Crossref API"""
        if not title or len(title) < 10:
            return None

        try:
            # Build query
            query = title[:50]  # Use title excerpt
            if authors:
                query = f"{authors[0]} {query}"

            url = CROSSREF_API.format(query.replace(' ', '+'))
            with urllib.request.urlopen(url, timeout=5) as response:
                data = json.loads(response.read().decode('utf-8'))

                # Get first result if available
                items = data.get('message', {}).get('items', [])
                if items:
                    return items[0].get('DOI')
        except Exception as e:
            self.stats['errors'].append(f"Crossref lookup {title[:30]}: {str(e)}")
            return None

        return None

    def resolve_unknown_author(self, article: Dict) -> Dict:
        """Resolve unknown author by looking up arXiv metadata"""
        has_unknown = any(
            au.get('name') == 'Unknown Author'
            for au in article.get('authors', [])
        )

        if not has_unknown:
            return article

        arxiv_id = article.get('arxiv_id')
        if not arxiv_id:
            # Try to extract from PDF filename
            pdf_path = article.get('local_pdf_path', '')
            match = re.search(r'(\d{4}\.\d{5})', pdf_path)
            if match:
                arxiv_id = match.group(1)

        if arxiv_id:
            metadata = self.fetch_arxiv_metadata(arxiv_id)
            if metadata and metadata.get('authors'):
                article['authors'] = [
                    {'name': name, 'affiliation': None}
                    for name in metadata['authors']
                ]
                self.stats['unknown_authors_resolved'] += 1
                time.sleep(0.5)  # Rate limit
                return article

        return article

    def fix_malformed_year(self, article: Dict) -> Dict:
        """Fix invalid year values"""
        year = article.get('year')

        if not year:
            return article

        # Check if already valid
        if isinstance(year, int) and 1800 <= year <= 2030:
            return article

        # Try inference methods
        arxiv_id = article.get('arxiv_id', '')
        inferred = self.infer_year_from_arxiv_id(arxiv_id)

        if not inferred:
            pdf_path = article.get('local_pdf_path', '')
            inferred = self.infer_year_from_filename(pdf_path)

        if inferred:
            article['year'] = inferred
            self.stats['years_fixed'] += 1

        return article

    def fix_generic_title(self, article: Dict) -> Dict:
        """Replace generic titles with real ones from arXiv"""
        title = article.get('title', '')

        if not (title.lower().startswith('paper_') or title == 'Unknown Title'):
            return article

        arxiv_id = article.get('arxiv_id')
        if arxiv_id:
            metadata = self.fetch_arxiv_metadata(arxiv_id)
            if metadata and metadata.get('title'):
                article['title'] = metadata['title']
                self.stats['titles_corrected'] += 1
                time.sleep(0.5)  # Rate limit

        return article

    def add_missing_doi(self, article: Dict) -> Dict:
        """Add DOI by querying Crossref"""
        if article.get('doi'):
            return article

        title = article.get('title', '')
        authors = [a.get('name') for a in article.get('authors', [])]

        doi = self.fetch_crossref_doi(title, authors)
        if doi:
            article['doi'] = doi
            self.stats['dois_added'] += 1
            time.sleep(0.5)  # Rate limit

        return article

    def standardize_arxiv_id(self, article: Dict) -> Dict:
        """Ensure arxiv_id is in canonical form"""
        arxiv_id = article.get('arxiv_id', '')

        if not arxiv_id:
            # Try to extract from ID
            article_id = article.get('id', '')
            if re.match(r'\d{4}\.\d{5}', article_id):
                article['arxiv_id'] = article_id

        return article

    def cleanse_all(self) -> Dict:
        """Execute full cleansing pipeline"""
        print(f"Starting cleansing of {len(self.articles)} articles...\n")

        for i, article in enumerate(self.articles):
            if i % 10 == 0:
                print(f"  Processing article {i+1}/{len(self.articles)}...", flush=True)

            article = self.resolve_unknown_author(article)
            article = self.fix_malformed_year(article)
            article = self.fix_generic_title(article)
            article = self.standardize_arxiv_id(article)
            article = self.add_missing_doi(article)

            self.articles[i] = article

        self.db['articles'] = self.articles
        return self.db

    def save_cleaned(self, output_path: str = None):
        """Save cleaned database"""
        if output_path is None:
            output_path = self.db_path.replace('.json', '_cleaned.json')

        with open(output_path, 'w') as f:
            json.dump(self.db, f, indent=2)

        print(f"\n✓ Cleaned database saved to: {output_path}")

    def report(self):
        """Print cleansing report"""
        print("\n=== CLEANSING REPORT ===")
        print(f"Unknown authors resolved: {self.stats['unknown_authors_resolved']}")
        print(f"Years fixed: {self.stats['years_fixed']}")
        print(f"DOIs added: {self.stats['dois_added']}")
        print(f"Titles corrected: {self.stats['titles_corrected']}")

        if self.stats['errors']:
            print(f"\nErrors encountered: {len(self.stats['errors'])}")
            for error in self.stats['errors'][:5]:
                print(f"  - {error}")

        print(f"\n✓ Cleansing complete")

def main():
    print("=" * 70)
    print("LOD PHASE 1: DATA CLEANSING PIPELINE")
    print("=" * 70)

    cleaner = LODCleaner()

    # Execute cleansing
    cleaner.cleanse_all()

    # Save cleaned database
    cleaner.save_cleaned()

    # Print report
    cleaner.report()

    print("\nNext steps:")
    print("1. Review rh_corpus_database_complete_cleaned.json")
    print("2. Compare with original to verify improvements")
    print("3. Move to Phase 2: Ontology Mapping")

if __name__ == '__main__':
    main()
