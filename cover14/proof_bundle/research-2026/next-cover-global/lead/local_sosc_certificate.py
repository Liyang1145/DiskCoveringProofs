"""Interval SOSC quadratic control; exact KKT identity premise in LOCAL-SOSC-PROOF.md.
Sparse 6variable AD per contact, full28x28 mixed quadratic form via penalty/LDL.
"""
import json,numpy as np
from pathlib import Path
from root_integer_certificate import I,Q,S
P=Path(__file__).resolve().parent;N=6
class J:
 def __init__(self,v,g=None,h=None):
  self.v=iv(v);self.g=g if g is not None else[I(0)for _ in range(N)];self.h=h if h is not None else[[I(0)for _ in range(N)]for _ in range(N)]
 @staticmethod
 def var(v,k):
  t=J(v);t.g[k]=I(1);return t
 def __add__(a,b):
  b=jet(b);return J(a.v+b.v,[a.g[i]+b.g[i]for i in range(N)],[[a.h[i][j]+b.h[i][j]for j in range(N)]for i in range(N)])
 __radd__=__add__
 def __neg__(a):return J(-a.v,[-x for x in a.g],[[-x for x in row]for row in a.h])
 def __sub__(a,b):return a+-jet(b)
 def __rsub__(a,b):return jet(b)+-a
 def __mul__(a,b):
  b=jet(b);return J(a.v*b.v,[a.g[i]*b.v+a.v*b.g[i]for i in range(N)],[[a.h[i][j]*b.v+a.g[i]*b.g[j]+a.g[j]*b.g[i]+a.v*b.h[i][j]for j in range(N)]for i in range(N)])
 __rmul__=__mul__
 def unary(a,v,d,dd):return J(v,[d*x for x in a.g],[[d*a.h[i][j]+dd*a.g[i]*a.g[j]for j in range(N)]for i in range(N)])
 def inv(a):
  v=a.v.inv();return a.unary(v,-v*v,2*v*v*v)
 def __truediv__(a,b):return a*jet(b).inv()
 def __rtruediv__(a,b):return jet(b)*a.inv()
 def sqrt(a):
  v=a.v.sqrt();return a.unary(v,1/(2*v),-1/(4*v*v*v))
 def __pow__(a,n):
  v=J(1)
  for _ in range(n):v=v*a
  return v
def iv(x):return x if isinstance(x,I)else I(x)
def jet(x):return x if isinstance(x,J)else J(x)
def mid(x):return (x.lo+x.hi)/(2*S)
def solve(M,v):
 A=[list(row)+[x]for row,x in zip(M,v)];n=len(v)
 for k in range(n):
  pivot=next(i for i in range(k,n)if A[i][k].lo*A[i][k].hi>0);A[k],A[pivot]=A[pivot],A[k]
  q=A[k][k];A[k]=[x/q for x in A[k]]
  for i in range(n):
   if i==k:continue
   q=A[i][k];A[i]=[x-q*y for x,y in zip(A[i],A[k])]
 return [row[-1]for row in A]
def norm(p):return sum(x*x for x in p)
def boundary(p,q,sign):
 dv=[q[k]-p[k]for k in range(2)];nn=norm(dv);k=(norm(q)-norm(p))/2;base=[v*k/nn for v in dv];rad=((1-norm(base))/nn).sqrt();anchor=[base[0]-sign*dv[1]*rad,base[1]+sign*dv[0]*rad]
 return norm([anchor[k]-p[k]for k in range(2)])
def circum(p,q,v):
 u=[q[k]-p[k]for k in range(2)];w=[v[k]-p[k]for k in range(2)];d=u[0]*w[1]-u[1]*w[0];aa=(norm(q)-norm(p))/2;bb=(norm(v)-norm(p))/2
 x=(aa*w[1]-u[1]*bb)/d;y=(u[0]*bb-aa*w[0])/d
 return (x-p[0])**2+(y-p[1])**2
# Exact derivativecontrol andoneknowncirclecontrol.
u=J.var(I(2),0);v=J.var(I(3),1);w=J.var(I(4),2);f=u*u*v+1/w
for val,q in[(f.h[0][1],4),(f.h[2][2],Q(1,32)),(f.g[0],12)]:assert val.lo<=Q(q)*S<=val.hi
f=circum([J(1),J(0)],[J(0),J(1)],[J(-1),J(0)]);assert f.v.lo<=S<=f.v.hi
cert=json.loads((P/'root-integer-certificate.json').read_text());z,c,r=[I(int(Q(a)*S),int(Q(b)*S),True)for a,b in cert['box_dyadic']];s=(1-r*r).sqrt();a=(s+z)/2;t=r+(r*r-z*z).sqrt();b=r+(r*r-(a-z)**2).sqrt();d=1-(r*r-c*c).sqrt()
C=[(sx*a,sy*b)for sx in(-1,1)for sy in(-1,1)]+[(sx*c,sy*d)for sx in(-1,1)for sy in(-1,1)]+[(-s,I(0)),(s,I(0)),(z,I(0)),(-z,I(0)),(I(0),-t),(I(0),t)]
g=json.loads((P/'stress-barycentric-result.json').read_text());grads=[];hess=[];strict_margins=[]
v1=(1+a*a+b*b-r*r)/2;v2=(1+c*c+d*d-r*r)/2;det=a*d-b*c
px=(v1*d-v2*b)/det;py=(a*v2-c*v1)/det
anchors=[(s,r),(px,py),(I(0),I(1)),(-px,py),(-s,r),(-s,-r),(-px,-py),(I(0),I(-1)),(px,-py),(s,-r)]
# Independent exact interval geometric controls for persistence of ALL selectedcontacts.
for kk,entry in enumerate(g['anchors']+g['faces']):
 ids=entry['owners']if kk<10 else entry['ids']
 if kk<10:wit=anchors[kk]
 else:
  p,q,v=[C[i]for i in ids];u=[q[j]-p[j]for j in range(2)];vv=[v[j]-p[j]for j in range(2)];dd=u[0]*vv[1]-u[1]*vv[0]
  aa=(norm(q)-norm(p))/2;bb=(norm(v)-norm(p))/2
  wit=[(aa*vv[1]-u[1]*bb)/dd,(u[0]*bb-aa*vv[0])/dd]
  assert (1-norm(wit)).lo>0
 for ii in range(14):
  if ii in ids:continue
  margin=norm([wit[j]-C[ii][j]for j in range(2)])-r*r
  assert margin.lo>0,(kk,ii)
  strict_margins.append(margin.lo)
 if kk<10:
  dv=[C[ids[1]][j]-C[ids[0]][j]for j in range(2)]
  transverse=-wit[1]*dv[0]+wit[0]*dv[1];assert transverse.lo*transverse.hi>0
for k,entry in enumerate(g['anchors']+g['faces']):
 ids=entry['owners']if k<10 else entry['ids'];nodes=[2*i+j for i in ids for j in range(2)];ps=[[J.var(C[i][j],2*l+j)for j in range(2)]for l,i in enumerate(ids)]
 if k<10:
  # Sign is EXACTdiscreteinputcheckedbyrootgeometry: chooseintervalpoint branch nearestreferenceangleproposal.
  angle=float(entry['theta']);p,q=[np.array([mid(x)for x in C[i]])for i in ids];dv=q-p;ba=dv*((q@q-p@p)/2/(dv@dv));sgn=1 if np.array([-dv[1],dv[0]])@(np.array([np.cos(angle),np.sin(angle)])-ba)>0 else -1
  # Certify proposed branch equals exactsymbolicanchor via signedperpendicularprojection.
  pp,qq=[C[i]for i in ids];dvI=[qq[j]-pp[j]for j in range(2)];baI=[x*((norm(qq)-norm(pp))/2/norm(dvI))for x in dvI]
  branch=-dvI[1]*(anchors[k][0]-baI[0])+dvI[0]*(anchors[k][1]-baI[1]);assert (sgn*branch).lo>0
  f=boundary(*ps,sgn)
 else:f=circum(*ps)
 assert (f.v-r*r).lo<=0<=(f.v-r*r).hi
 row=[I(0)for _ in range(28)];H=[[I(0)for _ in range(28)]for _ in range(28)]
 for i,ii in enumerate(nodes):
  row[ii]=f.g[i]
  for j,jj in enumerate(nodes):H[ii][jj]=f.h[i][j]
 grads.append(row);hess.append(H)
# Symmetric positiveorbits, squaredradiusgradient(positive, opposite toconstraintR-f).
orbits=[[0,4,5,9],[1,3,6,8],[2,7],[10,13,16,19],[12,15,18,21]]
# Exact incidence-orbit controls under signed-coordinate D2 action (nofloatmatching).
labels=[(sx,'a',sy,'b')for sx in(-1,1)for sy in(-1,1)]+[(sx,'c',sy,'d')for sx in(-1,1)for sy in(-1,1)]+[(-1,'s',0,'0'),(1,'s',0,'0'),(1,'z',0,'0'),(-1,'z',0,'0'),(0,'0',-1,'t'),(0,'0',1,'t')]
perms=[[labels.index((sx*lx,nx,sy*ly,ny))for lx,nx,ly,ny in labels]for sx,sy in[(1,1),(-1,1),(1,-1),(-1,-1)]]
contactkeys=[('B'if k<10 else'T',frozenset(e['owners']if k<10 else e['ids']))for k,e in enumerate(g['anchors']+g['faces'])]
for orb in orbits:
 typ,vs=contactkeys[orb[0]]
 actual={contactkeys.index((typ,frozenset(perm[i]for i in vs)))for perm in perms}
 assert actual==set(orb)
OG=[[sum((grads[i][j]for i in orb),I(0))for j in range(28)]for orb in orbits]
# Fourindependentphysicalequilibriumrows +sumallmultipliers1. Exactrank4 isanalyticpremise, notintervalzero test.
rows=[[OG[k][j]for k in range(5)]for j in range(28)]+[[I(len(orb))for orb in orbits]]
chosen=[28];mat=np.array([[mid(x)for x in row]for row in rows]);rank=1
for j in range(28):
 nr=np.linalg.matrix_rank(mat[chosen+[j]],tol=1e-9)
 if nr>rank:chosen.append(j);rank=nr
 if rank==5:break
assert rank==5;weights=solve([rows[j]for j in chosen],[I(int(j==28))for j in chosen]);assert all(w.lo>0 for w in weights)
lam=[I(0)for _ in range(24)]
for orb,w in zip(orbits,weights):
 for i in orb:lam[i]=w
HL=[[sum((lam[k]*hess[k][i][j]for k in range(24)),I(0))for j in range(28)]for i in range(28)]
# Penalty establishes positivityonFULLcriticalsubspace without claiming intervalrank.
positive=sum(orbits,[]);pen=I(1000)
A=[[HL[i][j]+pen*sum((grads[k][i]*grads[k][j]for k in positive),I(0))+I(1000*int(i==j==19))for j in range(28)]for i in range(28)]
# intervalLDL, allpivots>0 sufficespointwisepositive definite, includingmixedblocks.
L=[[I(int(i==j))for j in range(28)]for i in range(28)];diag=[]
for i in range(28):
 di=A[i][i]-sum((L[i][k]**2*diag[k]for k in range(i)),I(0));assert di.lo>0,(i,mid(di));diag.append(di)
 for j in range(i+1,28):L[j][i]=(A[j][i]-sum((L[j][k]*L[i][k]*diag[k]for k in range(i)),I(0)))/di
out={'status':'certified_SOSC_quadratic_control_conditional_exact_KKT_identity','scope':'literaltruecircumradiusbranch, arbitrary28sitecoordinates rotationgauge; exactKKTanalyticidentityneeded separately','positive_orbits':orbits,'selected_weight_rows':chosen,'weight_intervals':[w.dec()for w in weights],'penalty':1000,'LDL_pivots':[x.dec()for x in diag],'min_pivot_lower_display':min(x.lo/S for x in diag),'min_other_site_squared_separation_lower':str(Q(min(strict_margins),S)),'all_contact_branches_strict_nearest_and_persistent':True,'D2_orbit_incidence_checks':True}
(P/'local-sosc-certificate.json').write_text(json.dumps(out,indent=2));print('SOSC quadraticcontrolcertified conditional exactKKT, minLDL',out['min_pivot_lower_display'],'weights',[mid(w)for w in weights],flush=True)
