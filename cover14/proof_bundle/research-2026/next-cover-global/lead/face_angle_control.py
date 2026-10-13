"""Actual-cover calibration of interior dual angle identity and radius length compatibility."""
import json,math,numpy as np
from fractions import Fraction
from itertools import combinations
from pathlib import Path
P=Path(__file__).resolve().parent
D=json.loads((P/'improved-upper-test.json').read_text());G=json.loads((P/'stress-barycentric-result.json').read_text());C=np.array([[float(Fraction(x))for x in p]for p in D['centers']]);faces=[x['ids']for x in G['faces']]+[[4,6,12],[5,7,13]]
def angle(u,v):return math.atan2(abs(float(np.linalg.det(np.array([u,v])))),float(u@v))
W=[];R=[];E={};gammas={};lengthres=0
for j,f in enumerate(faces):
 a,b,c=C[f];w=np.linalg.solve(2*np.array([b-a,c-a]),np.array([b@b-a@a,c@c-a@a]));rad=np.linalg.norm(w-a);W.append(w);R.append(rad)
 for e in combinations(f,2):
  e=tuple(sorted(e));opp=next(i for i in f if i not in e);g=angle(C[e[0]]-C[opp],C[e[1]]-C[opp]);gammas[j,e]=g;E.setdefault(e,[]).append(j);lengthres=max(lengthres,abs(np.linalg.norm(C[e[0]]-C[e[1]])-2*rad*math.sin(g)))
rows=[]
for e,fs in E.items():
 if len(fs)!=2:continue
 i,j=fs;beta=angle(W[i]-C[e[0]],W[j]-C[e[0]]);pred=math.pi-gammas[i,e]-gammas[j,e];rows.append({'edge':e,'beta':beta,'prediction':pred,'error':beta-pred})
out={'status':'numeric_calibration_only','interior_edges':len(rows),'max_angle_residual':max(abs(x['error'])for x in rows),'max_length_residual':lengthres,'rows':rows}
(P/'face-angle-control.json').write_text(json.dumps(out,indent=2));print({k:v for k,v in out.items()if k!='rows'})
