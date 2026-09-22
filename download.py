import urllib.request
import re

url = 'https://link.springer.com/book/10.1007/978-3-540-85238-4'
req = urllib.request.Request(url, headers={'User-Agent': 'Mozilla/5.0'})
try:
    html = urllib.request.urlopen(req).read().decode('utf-8')
    for m in re.finditer(r'href="(/chapter/10\.1007/[^"]+)"[^>]*>(.*?)</a>', html, re.DOTALL):
        link, title = m.group(1), m.group(2)
        if any(k in title.lower() for k in ['kufleitner', 'forest', 'factor', 'height']):
            print('Found chapter:', link, title.strip())
except Exception as e:
    print('Error:', e)
