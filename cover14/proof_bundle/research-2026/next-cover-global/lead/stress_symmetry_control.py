"""Bounded numeric test: does D2 averaging force a unique candidate stress?
This can identify an all-stress convexity obstruction, but numeric rank isn't proof.
"""
import json,numpy as np
from fractions import Fraction
from pathlib import Path
P=Path(__file__).resolve().parent
g=json.loads((P/'stress-barycentric-result.json').read_text());dat=json.loads((P/'improved-upper-test.json').read_text());C=[tuple(Fraction(x)for x in p)for p in dat['centers']]
D=np.load(P/'stress-barycentric-matrix.npz');A,b=D['A'],D['b'];rows=[];perms=[]
edges=[(j,i)for j,x in enumerate(g['anchors'])for i in x['owners']];faces=[tuple(sorted(x['ids']))for x in g['faces']]
for sx,sy in[(-1,1),(1,-1)]:
 sites=[C.index((sx*x,sy*y))for x,y in C]
 anc=[next(k for k,y in enumerate(g['anchors'])if set(y['owners'])=={sites[i]for i in x['owners']})for x in g['anchors']]
 perm=[faces.index(tuple(sorted(sites[i]for i in f)))for f in faces]+[14+edges.index((anc[j],sites[i]))for j,i in edges];perms.append(perm)
 for i,j in enumerate(perm):
  row=np.zeros(37);row[i]+=1;row[j]-=1;rows.append(row)
AA=np.vstack((A,rows));bb=np.r_[b,np.zeros(len(rows))];x,res,rank,sv=np.linalg.lstsq(AA,bb,rcond=1e-12)
out={'status':'numeric_only','symmetric_linear_rank':int(rank),'unknown_count':37,'residual':float(max(abs(AA@x-bb))),'symmetry_permutations_weights':perms,'minimum_weight':float(min(x[:34])),'weights':x.tolist(),'scope':'linear uniqueness diagnostic at numeric root; not exact rank nor all-stress theorem'}
(P/'stress-symmetry-control.json').write_text(json.dumps(out,indent=2));print({k:v for k,v in out.items()if k not in('weights','symmetry_permutations_weights')})
