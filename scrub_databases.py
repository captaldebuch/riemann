import json

fake_keywords = ['team', 'group', 'researchers', 'various', 'unknown']

for filename in ['doc/html/rh_corpus_database.json', 'doc/html/rh_corpus_database_complete.json']:
    try:
        with open(filename, 'r') as f:
            data = json.load(f)
            
        articles_to_remove = set()
        
        for article in data.get('articles', []):
            title = article.get('title', '')
            if title.startswith('paper_') or title == '2309.09171v1':
                articles_to_remove.add(article.get('id'))
                continue
                
            authors = article.get('authors', [])
            for a in authors:
                name = a.get('name', '').lower()
                if any(kw in name for kw in fake_keywords):
                    articles_to_remove.add(article.get('id'))
                    break
                    
        # Filter articles
        data['articles'] = [a for a in data.get('articles', []) if a.get('id') not in articles_to_remove]
        
        # Filter other lists
        for key in ['insights', 'intuitions', 'formalization']:
            if key in data:
                data[key] = [x for x in data[key] if x.get('article_id') not in articles_to_remove]
                
        # Filter connections
        if 'connections' in data:
            data['connections'] = [x for x in data['connections'] if x.get('source_id') not in articles_to_remove and x.get('target_id') not in articles_to_remove]
            
        with open(filename, 'w') as f:
            json.dump(data, f, indent=2)
            
        print(f"Cleaned {filename}: removed {len(articles_to_remove)} junk records.")
    except Exception as e:
        print(f"Error processing {filename}: {e}")

