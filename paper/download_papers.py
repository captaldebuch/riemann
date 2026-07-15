import requests
import json
import time
import os
import re
import urllib.parse

def clean_filename(name):
    return re.sub(r'[^\w\-_\. ]', '_', name)

def search_openalex(query, year):
    # Search by title/author/year
    url = f"https://api.openalex.org/works?search={urllib.parse.quote(query)}"
    if year:
        url += f"&filter=publication_year:{year}"
    
    # Adding polite pool email
    url += "&mailto=antigravity@example.com"
    
    try:
        response = requests.get(url, timeout=10)
        response.raise_for_status()
        data = response.json()
        if data.get('results') and len(data['results']) > 0:
            best_match = data['results'][0]
            oa = best_match.get('open_access', {})
            pdf_url = oa.get('oa_url')
            if pdf_url and (pdf_url.endswith('.pdf') or 'arxiv.org/pdf' in pdf_url or 'pdf' in pdf_url.lower()):
                return pdf_url
            
            # Sometimes best_match['primary_location']['pdf_url'] is available
            primary = best_match.get('primary_location', {})
            if primary and primary.get('pdf_url'):
                return primary['pdf_url']
            
        return None
    except Exception as e:
        print(f"Error searching OpenAlex: {e}")
        return None

def download_pdf(url, filepath):
    try:
        headers = {'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64)'}
        response = requests.get(url, headers=headers, stream=True, timeout=15)
        response.raise_for_status()
        
        # Check if it's really a PDF or a webpage
        content_type = response.headers.get('content-type', '')
        if 'html' in content_type.lower():
            print(f"  -> URL points to HTML, skipping: {url}")
            return False
            
        with open(filepath, 'wb') as f:
            for chunk in response.iter_content(chunk_size=8192):
                f.write(chunk)
        return True
    except Exception as e:
        print(f"  -> Failed to download from {url}: {e}")
        return False

def main():
    os.makedirs('pdf', exist_ok=True)
    
    with open('papers_list.txt', 'r', encoding='utf-8') as f:
        lines = f.readlines()
    
    success_count = 0
    fail_count = 0
    
    # Skip header
    for line in lines[1:]:
        line = line.strip()
        if not line:
            continue
            
        parts = [p.strip() for p in line.split('|')]
        if len(parts) >= 4:
            author = parts[0]
            year = parts[1]
            venue = parts[2]
            contribution = parts[3]
            
            # Creating a good search query
            # We don't have the exact title in most cases, but we have the author, venue, year, and a description.
            # Wait, the table provided by the user has "Publication Title / Venue". Sometimes it's the title, sometimes it's the venue!
            # e.g., "The Distribution of Prime Numbers (CUP)" vs "Journal de Mathématiques Pures et Appliquées"
            # It's better to search with Author, Year, and the Venue/Title.
            query = f"{author} {venue} {contribution[:50]}"
            print(f"Searching: {author} ({year}) - {venue}")
            
            pdf_url = search_openalex(query, year)
            if pdf_url:
                print(f"  -> Found PDF URL: {pdf_url}")
                # Create a filename
                safe_author = clean_filename(author.split(',')[0].split('and')[0].strip())
                filename = f"pdf/{year}_{safe_author}.pdf"
                
                # Check if already downloaded
                if os.path.exists(filename):
                    print(f"  -> Already exists: {filename}")
                    success_count += 1
                    continue
                
                if download_pdf(pdf_url, filename):
                    print(f"  -> Successfully downloaded: {filename}")
                    success_count += 1
                else:
                    fail_count += 1
            else:
                print(f"  -> No Open Access PDF found.")
                fail_count += 1
                
        time.sleep(1) # Be polite to API
        
    print(f"\nDone. Successfully downloaded {success_count} papers. Failed/Not found: {fail_count}")

if __name__ == "__main__":
    main()
