"""Exact literal Voronoi incidence control and independent stored disk checks.
Does not certify cover-to-catalogue completeness by mere enumeration.
"""
import json,math,importlib.util,hashlib
from fractions import Fraction as F
from pathlib import Path
from collections import Counter,defaultdict
from itertools import combinations,permutations
P=Path(__file__).resolve().parents[1]
s=importlib.util.spec_from_file_location('u',P/'members/upper/py/repro_c411_independent.py');u=importlib.util.module_from_spec(s);s.loader.exec_module(u)
data=json.loads((P/'lead/improved-upper-test.json').read_text());C=[tuple(map(F,c))for c in data['centers']]
true=[]
for label,p in u.candidates(C):
 if not label.startswith('circum'):continue
 ids=tuple(map(int,label[6:].split(',')));_,x,y=p
 ds=[(x-a)**2+(y-b)**2 for a,b in C]
 if all(ds[k]==min(ds) for k in ids):true.append(ids)
# float used ONLY to propose cyclic ordering; exact determinant below validates it
ring=sorted(range(10),key=lambda i:math.atan2(float(C[i][1]),float(C[i][0])))
assert all(C[ring[i]][0]*C[ring[(i+1)%10]][1]-C[ring[i]][1]*C[ring[(i+1)%10]][0]>0 for i in range(10))
rel={v:i for i,v in enumerate(ring)};rel.update({i:i for i in range(10,14)})
faces=[tuple(sorted(rel[v]for v in f))for f in true]
def canon(fs,N,m):
 best=None
 for perm in permutations(range(m)):
  for sign in(-1,1):
   for shift in range(N):
    key=tuple(sorted(tuple(sorted((sign*v+shift)%N if v<N else N+perm[v-N]for v in f))for f in fs))
    if best is None or key<best:best=key
 return best
key=canon(faces,10,4)
cat=json.loads((P/'members/topology/k-catalogue-n14.json').read_text())
match=[];checked=0
for group,entries in cat.items():
 N,m=map(int,group.split('/'))
 for j,e in enumerate(entries):
  fs=[tuple(sorted(f))for f in e['faces']];assert len(fs)==len(set(fs))
  edges=Counter(tuple(sorted(ab))for f in fs for ab in combinations(f,2))
  boundary={tuple(sorted((i,(i+1)%N)))for i in range(N)}
  assert {ab for ab,n in edges.items()if n==1}==boundary
  assert all(n==1 if ab in boundary else n==2 for ab,n in edges.items())
  assert N+m-len(edges)+len(fs)==1
  for v in range(N+m):
   link=defaultdict(set)
   for f in fs:
    if v in f:
     a,b=[w for w in f if w!=v];link[a].add(b);link[b].add(a)
   seen=set();todo=[next(iter(link))]
   while todo:
    w=todo.pop()
    if w in seen:continue
    seen.add(w);todo.extend(link[w]-seen)
   assert len(seen)==len(link)
   deg=sorted(map(len,link.values()))
   if v<N:assert deg==[1,1]+[2]*(len(deg)-2)
   else:assert deg==[2]*len(deg)
  checked+=1
  if m==4 and tuple(sorted(fs))==key:match.append({'group':group,'index':j,'skeleton':e['skeleton']})
out={'checked_stored_complexes':checked,'exact_literal_nearest_triples':true,'ring_order':ring,'candidate_matches':match,'candidate_face_count':len(true),'scope':'stored complex validity and candidate membership, not standalone completeness proof'}
assert len(match)==1 and len(true)==16
(P/'lead/catalogue-audit.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
