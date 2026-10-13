"""Exact explicit quadratic minorant for balanced affineflow on a large anglebox.
No Hessian-continuum or optimalvalue smoothness premise. Norm radial splitting lemma.
"""
import json,numpy as np,hashlib
from fractions import Fraction as Q
from pathlib import Path
from root_integer_certificate import I,S,calibrate
from shared_radius_corner_fraction_kernel import sc
P=Path(__file__).resolve().parent;calibrate();src=P/'q10-adaptive-flow-interval.json';a=json.loads(src.read_text());audit=json.loads((P/'q10-adaptive-flow-fraction-audit.json').read_text());assert audit['source_sha256']==hashlib.sha256(src.read_bytes()).hexdigest()
z=[[Q(x)for x in v]for v in a['flow']];T=[[[Q(x)/4 for x in rr]for rr in e]for e in a['jet']];th=list(map(Q,a['theta0']));edges=json.loads((P/'q10-adaptive-flow-jet.json').read_text())['edges'];eps=Q('1/200');U=Q('.33173203427623414');pen=Q(3);kap=Q('1/100');caps=[[Q(int(i==5)-int(i==4))for i in range(10)],[Q(int(i==0)-int(i==9))for i in range(10)]]
def interval(a,b):return I(I(a).lo,I(b).hi,True)
def absup(a):return Q(max(abs(a.lo),abs(a.hi)),S)
def trig(t):
 sn,cs=sc(abs(t));sn=(-sn[1],-sn[0])if t<0 else sn;return[interval(*cs),interval(*sn)]
A=[trig(t)for t in th];H=[[I(pen*sum(c[i]*c[j]for c in caps))for j in range(10)]for i in range(10)];f0=I(0);g=[I(0)for _ in range(10)];rads=[]
for e in range(40):
 zz=[I(x)for x in z[e]];n=(sum(x*x for x in zz)).sqrt();u=[x/n for x in zz]
 along=[sum(u[k]*T[e][k][i]for k in range(2))for i in range(10)];lower=I(Q(n.lo,S)-eps*sum(map(absup,along)));assert lower.lo>0;rads.append(Q(lower.lo,S))
 cross=[-u[1]*T[e][0][i]+u[0]*T[e][1][i]for i in range(10)]
 f0-=U*n
 for i in range(10):
  g[i]-=U*along[i]
  for j in range(10):H[i][j]-=U*cross[i]*cross[j]/lower
 if edges[e]>=24:
  b=(edges[e]-24)//2;aa=A[b];der=[aa[1],-aa[0]];mix=[sum(der[k]*T[e][k][i]for k in range(2))for i in range(10)]
  # |w|<=eps sqrt(sum_k(||T_k||_1)^2), outward sqrt.
  wbound=eps*I(sum(sum(map(abs,T[e][k]))**2 for k in range(2))).sqrt()
  H[b][b]+=sum(aa[k]*zz[k]for k in range(2))-n*eps/3-wbound
  for i in range(10):H[b][i]+=mix[i];H[i][b]+=mix[i]
  f0-=sum(aa[k]*zz[k]for k in range(2))
  for i in range(10):g[i]-=sum(aa[k]*T[e][k][i]for k in range(2))
  g[b]+=sum(der[k]*zz[k]for k in range(2))
# ConstantmatrixH gives F>=f0+g.delta+.5delta^T(H-pen C^TC)delta onentirebox.
B=np.vstack([np.eye(9),-np.ones(9)]);mid=np.array([[(x.lo+x.hi)/(2*S)for x in rr]for rr in H]);W=B@np.linalg.inv(np.linalg.cholesky(B.T@(mid-float(kap)*np.eye(10))@B)).T
V=[[Q(format(W[i,j],'.17g'))for j in range(9)]for i in range(9)];V.append([-sum(V[i][j]for i in range(9))for j in range(9)])
HH=[[sum(V[k][i]*(H[k][l]-kap*int(k==l))*V[l][j]for k in range(10)for l in range(10))for j in range(9)]for i in range(9)]
rowbound=Q(max(sum(max(abs(HH[i][j].lo-int(i==j)*S),abs(HH[i][j].hi-int(i==j)*S))for j in range(9))for i in range(9)),S);assert rowbound<1
out=dict(status='certified_explicit_quadratic_minorant',source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),epsilon=str(eps),U=str(U),penalty=str(pen),kappa=str(kap),caps=[[str(x)for x in c]for c in caps],theta0=list(map(str,th)),flow=[[str(x)for x in e]for e in z],jet=[[[str(x)for x in rr]for rr in e]for e in T],edges=edges,radial_lowers=list(map(str,rads)),f0=f0.dec(),gradient=[x.dec()for x in g],H_intervals=[[x.dec()for x in rr]for rr in H],V=[[str(x)for x in rr]for rr in V],row_bound=str(rowbound),row_bound_display=float(rowbound),scope='F>=f0+g.delta+.005|delta|²-1.5sum(capnormal.delta)² for sumdelta=0, |delta|inf<=.005; allquantitiesexplicitrationalflow. F<=0 for r<=U original879witnesssystem.')
(P/'q10-quadratic-minorant-certificate.json').write_text(json.dumps(out,indent=2));print(out['status'],float(rowbound),'minrad',float(min(rads)))
