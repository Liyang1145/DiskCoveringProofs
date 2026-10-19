import urllib.request,concurrent.futures as cf,json
rows=[l.split() for l in open('ltar.txt')]
def head(r):
    m,f=r
    for c in ['mathlib4-master','mathlib4']:
        try:
            q=urllib.request.Request(f'https://lakecache.blob.core.windows.net/{c}/f/{f}',method='HEAD')
            with urllib.request.urlopen(q,timeout=30) as resp: return m,f,c,int(resp.headers['Content-Length'])
        except Exception as e: pass
    return m,f,None,0
with cf.ThreadPoolExecutor(48) as ex: res=list(ex.map(head,rows))
json.dump(res,open('sizes.json','w'))
print(len(res),sum(1 for r in res if r[2] is None),sum(r[3] for r in res))
