"""Exact combinatorial labelmatching only; no geometric equivalence from numericalradii."""
import json,itertools
from pathlib import Path
P=Path(__file__).resolve().parent;G=json.loads((P/'stress-barycentric-result.json').read_text());faces=[f['ids']for f in G['faces']]+[[4,6,12],[5,7,13]];owners=[a['owners']for a in G['anchors']];cycle=[next(iter(set(owners[i-1])&set(owners[i])))for i in range(10)];assert len(set(cycle))==10;hidden=sorted(set(range(14))-set(cycle));D=json.loads((P/'k10-catalogue-corrected.json').read_text());out=[]
for idx in [848,878,879]:
 target={tuple(sorted(f))for f in D['10/4'][idx]['faces']};matches=[]
 for shift in range(10):
  for sign in [-1,1]:
   for perm in itertools.permutations(range(10,14)):
    mapping={v:(shift+sign*j)%10 for j,v in enumerate(cycle)};mapping.update(zip(hidden,perm));ff={tuple(sorted(mapping[v]for v in f))for f in faces}
    if ff==target:matches.append(mapping)
 out.append({'index':idx,'exact_matches':matches})
(P/'candidate-catalogue-match.json').write_text(json.dumps({'scope':'literal16facecomplex graphisomorphism underboundarydihedral andhiddenpermutation','boundary_cycle':cycle,'hidden':hidden,'runs':out},indent=2));print([(r['index'],len(r['exact_matches']))for r in out])
