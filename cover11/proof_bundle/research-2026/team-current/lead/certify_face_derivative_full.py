"""Exhaustive finite interval proof for saturated face-1 branch dV/ddelta>0.
Rectangular parameter box over-approximates legal b upper by acos(.375); each delta box is intersected with [-b2,b1].
Necessary filters in ev are only used to discard boxes certainly outside the feasible branch. Every retained box is certified if derivative lower>0; otherwise recursively bisected.
"""
from certify_face_derivative import ev
from interval_joint_patch import I
import math,json,time,heapq,hashlib
from pathlib import Path
P=Path(__file__).parent
RLO=.375;RHI=.38;BLO=1.;BHI=1.1863995522992576
# initial reasonably fine; total 13344 boxes
NR,NB,ND=4,12,24
q=[]
for i in range(NR):
 r=I(RLO+(RHI-RLO)*i/NR,RLO+(RHI-RLO)*(i+1)/NR)
 for j in range(NB):
  b1=I(BLO+(BHI-BLO)*j/NB,BLO+(BHI-BLO)*(j+1)/NB)
  for k in range(NB):
   b2=I(BLO+(BHI-BLO)*k/NB,BLO+(BHI-BLO)*(k+1)/NB)
   for l in range(ND):
    d=I(-BHI+2*BHI*l/ND,-BHI+2*BHI*(l+1)/ND)
    lo=max(d.a,-b2.b);hi=min(d.b,b1.b)
    if lo<=hi:q.append([r,b1,b2,I(lo,hi)])
stack=[(x,0) for x in q];counts={'initial':len(q),'positive':0,'infeasible':0,'bisected':0,'remaining':0};maxdep=0;minpos=1e9
while stack:
 x,dep=stack.pop();maxdep=max(maxdep,dep);v=ev(x)
 if v is None:counts['infeasible']+=1;continue
 if v.a>0:counts['positive']+=1;minpos=min(minpos,float(v.a));continue
 if dep>=20:
  counts['remaining']+=1;print('UNRESOLVED',[(float(y.a),float(y.b))for y in x],v);continue
 k=max(range(4),key=lambda i:float(x[i].b-x[i].a));m=(x[k].a+x[k].b)/2
 for side in [0,1]:
  y=x.copy();y[k]=I(x[k].a,m) if side==0 else I(m,x[k].b);stack.append((y,dep+1))
 counts['bisected']+=1
out={'scope':'saturatedface1derivative; physicalhighbearingdomainoverapproximatedrectangularbox; proofcandidate','counts':counts,'maxdepth':maxdep,'min_positive_lower':minpos,'source_sha256':hashlib.sha256((P/'certify_face_derivative.py').read_bytes()).hexdigest(),'status':'proved-interval' if counts['remaining']==0 else 'unresolved'}
(P/'face_derivative_certificate.json').write_text(json.dumps(out,indent=2));print(out)
