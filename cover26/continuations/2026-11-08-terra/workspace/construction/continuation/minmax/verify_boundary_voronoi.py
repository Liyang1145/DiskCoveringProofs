import json
from pathlib import Path
from fractions import Fraction as F
p=Path(__file__).resolve().parent; d=json.loads((p/'rational_geometry.json').read_text(encoding='utf8')); C=[tuple(map(F,x)) for x in d['centers']];Q=[tuple(map(F,x)) for x in d['boundary_anchors']];R=F(d['radius'])
def dot(a,b):return a[0]*b[0]+a[1]*b[1]
def sgn(a,b=F(0),q=F(0)):
 assert q>=0
 if not b or not q:return (a>0)-(a<0)
 if not a:return (b>0)-(b<0)
 if (a>0)==(b>0):return (a>0)-(a<0)
 z=a*a-b*b*q
 return ((z>0)-(z<0))*((a>0)-(a<0))
rows=[]
for i in range(16):
 j=(i+1)%16;a=C[i];b=C[j];u=(b[0]-a[0],b[1]-a[1]);L=dot(u,u);h=(dot(b,b)-dot(a,a))/2;D=L-h*h;assert D>0
 xa=h*u[0]/L;ya=h*u[1]/L;xb=-u[1]/L;yb=u[0]/L
 # Choose the intersection in the same open half-plane as its rational anchor.
 if sgn(xa*Q[i][0]+ya*Q[i][1],xb*Q[i][0]+yb*Q[i][1],D)<0: xb=-xb;yb=-yb
 for k,c in enumerate(C):
  const=dot(a,a)-dot(c,c)-2*((a[0]-c[0])*xa+(a[1]-c[1])*ya)
  coeff=-2*((a[0]-c[0])*xb+(a[1]-c[1])*yb)
  assert (sgn(const,coeff,D)==0 if k in (i,j) else sgn(const,coeff,D)<0),(i,k)
 const=1+dot(a,a)-2*(a[0]*xa+a[1]*ya)-R*R;coef=-2*(a[0]*xb+a[1]*yb)
 assert sgn(const,coef,D)<0
 rows.append({'between_centers':[i,j],'x':[''+str(xa),str(xb)],'y':[str(ya),str(yb)],'sqrt_radicand':str(D)})
(p/'exact_boundary_voronoi.json').write_text(json.dumps({'convention':'x=x[0]+x[1]*sqrt(sqrt_radicand), likewise y','vertices':rows,'source':'rational_geometry.json'},indent=2)+'\n',encoding='utf8')
print('PASS: 16 distinct adjacent-pair exact boundary Voronoi vertices; all strictly inside declared radius')

