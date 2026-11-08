import json
from fractions import Fraction as F
from pathlib import Path
p=Path(__file__).resolve().parent; d=json.loads((p/'rational_geometry.json').read_text()); C=[tuple(map(F,x)) for x in d['centers']]; Q=[tuple(map(F,x)) for x in d['boundary_anchors']]; R=F(d['radius'])
def sub(a,b):return a[0]-b[0],a[1]-b[1]
def dot(a,b):return a[0]*b[0]+a[1]*b[1]
def cross(a,b):return a[0]*b[1]-a[1]*b[0]
def circ(a,b,c):
 u=sub(b,a);v=sub(c,a);D=2*cross(u,v);h=dot(b,b)-dot(a,a);k=dot(c,c)-dot(a,a);return ((h*v[1]-k*u[1])/D,(u[0]*k-v[0]*h)/D)
vals=[]
for f in d['faces']:
 q=circ(*(C[i] for i in f)); vals.append(dot(sub(q,C[f[0]]),sub(q,C[f[0]])))
for i,q in enumerate(Q):
 for j in [i,(i+1)%16]: vals.append(dot(sub(q,C[j]),sub(q,C[j])))
print('squared min',float(min(vals)),'max',float(max(vals)),'R squared',float(R*R),'radius range',float(min(vals))**.5,float(max(vals))**.5,'max shortfall', float(R*R-min(vals)))
print('slack faces:',[(f,round(float(v)**.5,9)) for f,v in zip(d['faces'],vals) if float(v)<float(R*R)-1e-7])
print('slack anchors:',[(i,j,round(float(dot(sub(q,C[j]),sub(q,C[j])))**.5,9)) for i,q in enumerate(Q) for j in (i,(i+1)%16) if float(dot(sub(q,C[j]),sub(q,C[j]))) < float(R*R)-1e-7])
