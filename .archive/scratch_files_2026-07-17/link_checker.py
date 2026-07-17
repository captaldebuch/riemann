import os
import re

root_dir = 'doc/html'

def check_links():
    missing_links = []
    
    # Regex to find href="..." and src="..."
    link_pattern = re.compile(r'(?:href|src)=["\']([^"\']+)["\']')
    
    for dirpath, _, filenames in os.walk(root_dir):
        for filename in filenames:
            if not filename.endswith(('.html', '.js')):
                continue
                
            filepath = os.path.join(dirpath, filename)
            
            try:
                with open(filepath, 'r', encoding='utf-8') as f:
                    content = f.read()
            except UnicodeDecodeError:
                continue
                
            links = link_pattern.findall(content)
            
            for link in links:
                # Ignore external links and anchors
                if link.startswith(('http://', 'https://', 'mailto:', 'javascript:', 'data:', '#')):
                    continue
                
                # Ignore empty links
                if not link:
                    continue
                    
                # Remove anchor from link if present
                clean_link = link.split('#')[0]
                if not clean_link:
                    continue
                
                # Resolve path
                if filepath.endswith('.js') and 'app.js' in filepath:
                    # app.js is loaded in index.html, so links inside app.js are relative to doc/html/
                    target_path = os.path.normpath(os.path.join(root_dir, clean_link))
                else:
                    # Resolve relative to the file containing the link
                    target_path = os.path.normpath(os.path.join(dirpath, clean_link))
                
                if not os.path.exists(target_path):
                    missing_links.append(f"File: {filepath}\nBroken Link: {link}\nResolved Path: {target_path}\n")

    if missing_links:
        print("Found broken links:")
        for msg in set(missing_links):
            print(msg)
    else:
        print("All local links are valid!")

if __name__ == '__main__':
    check_links()
