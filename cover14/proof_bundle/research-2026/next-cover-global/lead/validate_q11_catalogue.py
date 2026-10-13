import json
from pathlib import Path
from collections import Counter,defaultdict
from itertools import combinations
P=Path(__file__).resolve().parent
data=json.loads((P/'q11-pocket-catalogue.json').read_text());hist=Counter();alloc=Counter()
for entry in data['entries']:
 fs=[tuple(sorted(f))for f in entry['faces']];assert len(fs)==15==len(set(fs))
 edges=Counter(tuple(sorted(ab))for f in fs for ab in combinations(f,2))
 boundary={tuple(sorted((i,(i+1)%11)))for i in range(11)}
 assert {ab for ab,n in edges.items()if n==1}==boundary
 assert all(n==(1 if e in boundary else 2)for e,n in edges.items())
 assert 14-len(edges)+15==1
 chords=[e for e in edges if max(e)<11 and e not in boundary]
 assert all(min(b-a,11-(b-a))==2 for a,b in chords)
 for v in range(14):
  link=defaultdict(set)
  for f in fs:
   if v in f:
    a,b=[w for w in f if w!=v];link[a].add(b);link[b].add(a)
  seen=set();todo=[next(iter(link))]
  while todo:
   w=todo.pop()
   if w in seen:continue
   seen.add(w);todo.extend(link[w]-seen)
  assert seen==set(link)
  deg=sorted(map(len,link.values()))
  assert deg==([1,1]+[2]*(len(deg)-2) if v<11 else [2]*len(deg))
 hist[len(chords)]+=1;alloc[entry['piece_hub_counts'][0]]+=1
out={'checked':len(data['entries']),'by_chord_count':dict(sorted(hist.items())),'by_central_hub_count':dict(sorted(alloc.items())),'all_disk_links_edges_euler_valid':True,'scope':'conditional q11 combinatorial family; no metric exclusions'}
(P/'q11-pocket-validation.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
