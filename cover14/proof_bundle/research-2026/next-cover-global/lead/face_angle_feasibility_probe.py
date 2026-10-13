"""Bounded test: do discarded face-angle equations reject saved relaxedangle proposals?"""
import json,math,numpy as np
from itertools import combinations
from fractions import Fraction as Q
from scipy.optimize import linprog
from pathlib import Path
P=Path(__file__).resolve().parent
D10=json.loads((P/'k10-catalogue-corrected.json').read_text());D11=json.loads((P/'q11-pocket-catalogue.json').read_text());saved=[json.loads(x)for x in(P/'innernorm-combined-catalogue.jsonl').read_text().splitlines()];out=[]
for fam in ['10/4','11/3']:
 rr=sorted([x for x in saved if x['family']==fam and x['status']=='inconclusive'],key=lambda x:x['upper_display'])[:6]
 for row in rr:
  q=int(fam.split('/')[0]);idx=row['index'];faces=D11['entries'][idx]['faces']if q==11 else D10[fam][idx]['faces'];edges=sorted({tuple(sorted(e))for f in faces for e in combinations(f,2)});t=list(map(float,map(Q,row['rational_angles'])));var=[(i,v)for i,f in enumerate(faces)for v in f];pos={v:j for j,v in enumerate(var)};eq=[];rhs=[]
  for i,f in enumerate(faces):
   z=np.zeros(len(var))
   for v in f:z[pos[i,v]]=1
   eq.append(z);rhs.append(math.pi)
  for v in range(q,14):
   z=np.array([float(w==v)for i,w in var]);eq.append(z);rhs.append(2*math.pi)
  for j,e in enumerate(edges):
   fs=[(i,f)for i,f in enumerate(faces)if all(v in f for v in e)]
   if len(fs)!=2:continue
   z=np.zeros(len(var))
   for i,f in fs:z[pos[i,next(v for v in f if v not in e)]]=1
   eq.append(z);rhs.append(math.pi-t[q+j])
  lp=linprog(np.zeros(len(var)),A_eq=eq,b_eq=rhs,bounds=[(0,math.pi)]*len(var),method='highs');rec={'family':fam,'index':idx,'numeric_proposal_feasible':bool(lp.success),'message':lp.message};out.append(rec);print(fam,idx,lp.success,flush=True)
(P/'face-angle-feasibility-probe.json').write_text(json.dumps({'status':'numeric_only','scope':'12savedrelaxationproposals; rejectionnotgraphexclusion','runs':out},indent=2))
