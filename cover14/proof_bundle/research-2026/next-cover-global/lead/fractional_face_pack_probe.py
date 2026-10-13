"""Boundednumeric edge-disjointface deficits; no rigorous exclusion claimed."""
import json,math,time
import numpy as np
from scipy.optimize import linprog
from itertools import combinations
from fractions import Fraction as Q
from face_deficit_probe import solve,P
D10=json.loads((P/'k10-catalogue-corrected.json').read_text());D11=json.loads((P/'q11-pocket-catalogue.json').read_text());rows=[json.loads(x)for x in(P/'joint-innernorm-catalogue.jsonl').read_text().splitlines()];ret={(x['family'],x['index'])for x in json.loads((P/'all-face-pack-provisional-retained.json').read_text())['retained']};out=[];a=.33173203427623414**2
for fam in ['10/4','11/3']:
 rr=sorted([x for x in rows if (x['family'],x['index'])in ret and x['family']==fam],key=lambda x:x['upper_display'])[:6]
 for row in rr:
  q=int(fam.split('/')[0]);idx=row['index'];faces=D11['entries'][idx]['faces']if q==11 else D10[fam][idx]['faces'];edges=sorted({tuple(sorted(e))for f in faces for e in combinations(f,2)});y=list(map(float,map(Q,row['rational_potentials'])));t=list(map(float,map(Q,row['rational_angles'])));cnt={e:sum(all(v in f for v in e)for f in faces)for e in edges};tests=[]
  for j,f in enumerate(faces):
   ee={tuple(sorted(e))for e in combinations(f,2)}
   pot=[sum(y[v]for v in e)for e in ee];old=0
   for e,pp in zip(ee,pot):
    x=t[q+edges.index(e)];old+=a*(math.sin(x)-x*math.cos(x))+math.pi*max(0,a*math.cos(x)-pp)
   delta=solve(pot,2000)-old
   tests.append((j,ee,delta))
  mat=np.array([[int(e in ee) for j,ee,d in tests]for e in edges]);lp=linprog([d for j,ee,d in tests],A_ub=mat,b_ub=np.ones(len(edges)),bounds=(0,None),method='highs');assert lp.success
  best=(float(lp.fun),[(tests[j][0],float(v)) for j,v in enumerate(lp.x) if v>1e-8])
  rec={'family':fam,'index':idx,'old_upper':row['upper_display'],'delta':best[0],'faces':best[1],'numeric_new_upper':row['upper_display']+best[0]};out.append(rec);print(rec,flush=True)
(P/'fractional-face-pack-probe.json').write_text(json.dumps({'status':'numeric_only','runs':out},indent=2))
