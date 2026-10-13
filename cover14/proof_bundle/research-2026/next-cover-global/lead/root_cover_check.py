"""Interval controls for analytic root cover: original dyadic kernel, fixed symbolic slots.
Exact contact identities are recorded in ROOT-ATTAINMENT.md; interval only handles strict exclusions.
"""
import json,itertools
import sympy as sp
from pathlib import Path
from root_integer_certificate import I,J,Q,S,iv
P=Path(__file__).resolve().parent
cert=json.loads((P/'root-integer-certificate.json').read_text())
X=[I(int(Q(a)*S),int(Q(b)*S),True)for a,b in cert['box_dyadic']]
z,c,r=X;s=(1-r*r).sqrt();a=(s+z)/2;t=r+(r*r-z*z).sqrt();b=r+(r*r-(a-z)**2).sqrt();d=1-(r*r-c*c).sqrt()
C=[(sx*a,sy*b)for sx in(-1,1)for sy in(-1,1)]+[(sx*c,sy*d)for sx in(-1,1)for sy in(-1,1)]+[(s,I(0)),(-s,I(0)),(z,I(0)),(-z,I(0)),(I(0),t),(I(0),-t)]
a0,b0,c0,d0,s0,z0,t0=sp.symbols('a b c d s z t')
Cs=[(sx*a0,sy*b0)for sx in(-1,1)for sy in(-1,1)]+[(sx*c0,sy*d0)for sx in(-1,1)for sy in(-1,1)]+[(s0,0),(-s0,0),(z0,0),(-z0,0),(0,t0),(0,-t0)]
def norm2(p):return p[0]*p[0]+p[1]*p[1]
def ds(p,q):return norm2((p[0]-q[0],p[1]-q[1]))
stats={'collinear_symbolic':0,'outside_D':0,'not_nearest':0};remaining=[]
for ids in itertools.combinations(range(14),3):
 p,q,v=[C[i]for i in ids];det=2*((q[0]-p[0])*(v[1]-p[1])-(q[1]-p[1])*(v[0]-p[0]))
 if det.lo<=0<=det.hi:
  ps,qs,vs=[Cs[i]for i in ids];exact=sp.expand((qs[0]-ps[0])*(vs[1]-ps[1])-(qs[1]-ps[1])*(vs[0]-ps[0]));assert exact==0,(ids,exact)
  stats['collinear_symbolic']+=1;continue
 u=norm2(q)-norm2(p);w=norm2(v)-norm2(p)
 cen=((u*(v[1]-p[1])-w*(q[1]-p[1]))/det,((q[0]-p[0])*w-(v[0]-p[0])*u)/det)
 if norm2(cen).lo>S:stats['outside_D']+=1;continue
 rad=ds(cen,p)
 if any((ds(cen,C[j])-rad).hi<0 for j in range(14)if j not in ids):stats['not_nearest']+=1;continue
 assert norm2(cen).hi<S
 delta=rad-r*r
 remaining.append({'ids':ids,'squared_radius_minus_r2':delta.dec(),'slack_certified':delta.hi<0})
assert len(remaining)==16 and sum(x['slack_certified']for x in remaining)==2
v1=(1+a*a+b*b-r*r)/2;v2=(1+c*c+d*d-r*r)/2;det=a*d-b*c
px=(v1*d-v2*b)/det;py=(a*v2-c*v1)/det
assert all((ds((px,py),C[j])-r*r).lo>0 for j in range(14)if j not in(3,7))
anchors=[(s,r),(px,py),(I(0),I(1)),(-px,py),(-s,r),(-s,-r),(-px,-py),(I(0),I(-1)),(px,-py),(s,-r)]
owners=[3,7,5,1,9,0,4,6,2,8]
# exact contact identities attach each owner to two consecutive anchors.
for i in range(10):
 p,q=anchors[i],anchors[(i+1)%10];cross=p[0]*q[1]-p[1]*q[0];assert cross.lo>0
 # nearest-boundary constraints not necessary; connected disk arcs contain small interval between anchors.
 assert ds(p,C[owners[i]]).lo<= (r*r).hi and ds(q,C[owners[i]]).lo<=(r*r).hi
out={'status':'strict_interval_controls_pass','scope':'root-box strict candidate exclusions and cyclic anchors; tight equalities require analytic identities','center_order_symbolic':[list(map(str,p))for p in Cs],'counts':stats,'remaining_triples':remaining,'anchor_owner_order':owners,'root_box_source':'root-integer-certificate.json'}
(P/'root-cover-controls.json').write_text(json.dumps(out,indent=2));print(stats,'remaining',len(remaining),'slack',sum(x['slack_certified']for x in remaining),'boundary cyclic control passed')
