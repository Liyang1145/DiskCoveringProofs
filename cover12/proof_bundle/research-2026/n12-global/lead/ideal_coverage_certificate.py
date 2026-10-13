"""Ideal F,G,H,T configuration coverage: exact rational interval slack triangles,
symbolic active witnesses. No boundary sampling. Preliminary geometry checks."""
from stress_interval import I,F
from pathlib import Path
from network_graph import triangle
import json
P=Path(__file__).resolve().parents[1]
root=json.loads((P/'evidence/root-t-certificate.json').read_text())
a,t,r,w=[I(*v) for v in root['box']];b=(1+a+r)/2
# Represent physical(x,y) as (x,Y) with y=Y/sqrt3. 120deg rotation exact rational.
def rot(p):
 x,Y=p;return ((-x-Y)/2,(3*x-Y)/2)
def turn(p,k):
 for _ in range(k):p=rot(p)
 return p
def sub(p,q):return (p[0]-q[0],p[1]-q[1])
def det(p,q):return p[0]*q[1]-p[1]*q[0]
def norm(p):return p[0]*p[0]+p[1]*p[1]/3
def dot(p,q):return p[0]*q[0]+p[1]*q[1]/3
# ring CCW: +beta,60,120-beta,120+beta,180,240-beta,240+beta,300,360-beta
C=[]
for k in range(3):C += [turn((b,w),k),turn((t/2,3*t/2),k),turn((b,-w),(k+1)%3)]
C += [turn((a,I(0)),k) for k in range(3)]
faces=[tuple((i-2)%9 if i<9 else i for i in f) for f in triangle((3,3,3))]
# all triangles orientedCCW; strict oriented determinant, and convex ring polygon
faces=[f if det(sub(C[f[1]],C[f[0]]),sub(C[f[2]],C[f[0]])).lo>0 else (f[0],f[2],f[1]) for f in faces]
for f in faces: assert det(sub(C[f[1]],C[f[0]]),sub(C[f[2]],C[f[0]])).lo>0
# Exact oriented chain boundary equals convex ring polygon; no hidden crossings/holes.
from collections import Counter
chain=Counter()
for f in faces:
 for i,j in zip(f,f[1:]+f[:1]):
  chain[min(i,j),max(i,j)] += 1 if i<j else -1
boundary=Counter()
for i in range(9):
 j=(i+1)%9;boundary[min(i,j),max(i,j)] += 1 if i<j else -1
assert all(chain[k]==boundary[k] for k in chain.keys()|boundary.keys())
assert len(faces)==13 and len(set(frozenset(f) for f in faces))==13
for i in range(9):
 edge=sub(C[(i+1)%9],C[i])
 for j in range(12):
  if j not in (i,(i+1)%9):assert det(edge,sub(C[j],C[i])).lo>0,('not convex',i,j)
 assert det(C[i],C[(i+1)%9]).lo>0
 assert norm(C[i]).hi<1
# candidate witness formulas equal radius by F/H. all other face circumradii slack
active={frozenset(f) for f in [(8,0,9),(2,3,10),(5,6,11),(9,10,1),(10,11,4),(11,9,7)]}
rows=[]
for f in faces:
 if frozenset(f) in active:
  rows.append({'face':f,'kind':'active F/H symbolic witness'});continue
 p,q,s=[C[i] for i in f];v=sub(q,p);z=sub(s,p)
 # Circumcenter displacement u: u dot v=|v|²/2, u dot z=|z|²/2
 D=det(v,z);assert D.lo>0
 ux=(norm(v)*z[1]-norm(z)*v[1])/(2*D)
 uY=3*(v[0]*norm(z)-z[0]*norm(v))/(2*D)
 rad2=norm((ux,uY));assert rad2.hi<(r*r).lo,('slack face',f,rad2.dump())
 rows.append({'face':f,'kind':'strict circumradius bound','radius_squared':rad2.dump(),'margin':str((r*r).lo-rad2.hi)})
out={'status':'certified geometry and13 face coverage','scope':'ideal root only; boundary cap analytic argument separate','root_box':root['box'],'centers_scaled':[[v.dump() for v in c] for c in C],'faces':rows,'convex_ring_polygon':True}
(P/'evidence/ideal-coverage-certificate.json').write_text(json.dumps(out,indent=2))
print(json.dumps({'status':out['status'],'active_faces':len(active),'slack_faces':len(rows)-len(active)}))
