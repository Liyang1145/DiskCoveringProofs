import json,math
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
here=Path(__file__).resolve().parent
src=here.parents[2]/'minmaxarena'/'n26-origin-certificate.json'
d=json.loads(src.read_text(encoding='utf8')); C=[tuple(map(F,p)) for p in d['centers']]; r=F(d['radius']);
def sub(a,b):return a[0]-b[0],a[1]-b[1]
def dot(a,b):return a[0]*b[0]+a[1]*b[1]
def cross(a,b):return a[0]*b[1]-a[1]*b[0]
def circum(a,b,c):
 u=sub(b,a);v=sub(c,a);D=2*cross(u,v)
 if not D:return None
 h=dot(b,b)-dot(a,a);k=dot(c,c)-dot(a,a)
 return ((h*v[1]-k*u[1])/D,(u[0]*k-v[0]*h)/D)
faces=[]; other=[]
for f in combinations(range(26),3):
 p=circum(*(C[i] for i in f))
 if p is None or dot(p,p)>1:continue
 v=dot(sub(p,C[f[0]]),sub(p,C[f[0]]))
 if all(dot(sub(p,q),sub(p,q))>=v for q in C): faces.append(f)
print('active faces',len(faces)); assert len(faces)==34
Q=[]
for i in range(16):
 a,b=C[i],C[(i+1)%16];u=sub(b,a);L=dot(u,u);h=(dot(b,b)-dot(a,a))/2
 bx=float(h*u[0]/L);by=float(h*u[1]/L); k=math.sqrt(float(L-h*h))/float(L);ux=float(u[0]);uy=float(u[1]); options=[(bx-k*uy,by+k*ux),(bx+k*uy,by-k*ux)]
 x,y=max(options,key=lambda p:p[0]*float(a[0]+b[0])+p[1]*float(a[1]+b[1]))
 if x>-.5:
  z=F(round((y/(1+x))*10**12),10**12); q=((1-z*z)/(1+z*z),2*z/(1+z*z))
 else:
  z=F(round((y/(1-x))*10**12),10**12); q=((z*z-1)/(1+z*z),2*z/(1+z*z))
 assert dot(q,q)==1
 assert all(dot(sub(q,C[j]),sub(q,C[j]))<=r*r for j in (i,(i+1)%16)),i
 Q.append(q)
print('boundary anchors',len(Q))
result={'radius':str(r),'centers':[[str(x),str(y)] for x,y in C],'boundary_center_order':list(range(16)), 'boundary_anchors':[[str(x),str(y)] for x,y in Q], 'faces':[list(f) for f in faces], 'status':'Rational witnesses proposed using floating-point circle intersections; validated exactly by verify_triangles.py; no old exact-root identification.'}
(here/'rational_geometry.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')
