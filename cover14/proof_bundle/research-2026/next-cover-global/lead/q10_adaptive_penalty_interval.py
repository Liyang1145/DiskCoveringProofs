"""Exact balanced affine-flow Hessian certificate on a rational-angle box, sumzero gauge."""
import json,sys,math,numpy as np
from fractions import Fraction as F
from collections import deque
from root_integer_certificate import I,S,calibrate
from shared_radius_corner_fraction_kernel import sc
from pathlib import Path
P=Path(__file__).resolve().parent;calibrate()
import q11_chord_flow_fraction_replay as fr
jet=json.loads((P/'q10-adaptive-flow-jet.json').read_text());row=json.loads((P/'q10-relaxed-anchor-probe.json').read_text())['rows'][0]
D=np.array(row['incidence_matrix'],int)[jet['edges']][:,[i for i in range(22)if i not in[8,9]]].tolist();m=40;nv=20
# Repair every coefficient column by tree balance, exact Fraction.
def repair(z):
 adj=[[]for _ in range(nv+1)];root=nv
 for e,dr in enumerate(D):
  u=dr.index(1);v=dr.index(-1)if -1 in dr else root;adj[u].append((v,e));adj[v].append((u,e))
 parent={root:None};order=[root]
 for u in order:
  for v,e in adj[u]:
   if v not in parent:parent[v]=(u,e);order.append(v)
 assert len(order)==nv+1
 bal=[sum(D[e][u]*z[e]for e in range(m))for u in range(nv)]
 for u in reversed(order[1:]):
  v,e=parent[u];cor=-bal[u]/D[e][u];z[e]+=cor
  if v!=root:bal[v]+=D[e][v]*cor
  bal[u]=F(0)
 assert all(sum(D[e][u]*z[e]for e in range(m))==0 for u in range(nv))
 return z
zf=np.array(jet['baseflow']);tf=np.array(jet['jet']).reshape(40,2,10)
z0=[[F(0)]*2 for _ in range(40)];T=[[[F(0)]*10 for _ in range(2)]for _ in range(40)]
for k in range(2):
 col=repair([F(format(x,'.17g'))for x in zf[:,k]])
 for e in range(40):z0[e][k]=col[e]
 for j in range(10):
  col=repair([F(format(x,'.17g'))for x in tf[:,k,j]])
  for e in range(40):T[e][k][j]=col[e]
th=[F(format(math.atan2(a[1],a[0]),'.17g'))for a in row['anchors']]
U=F('.33173203427623414');eps=F(sys.argv[1]if len(sys.argv)>1 else'1/100000');kappa=F('1/100'); penalty=F(3); caps=[[F(int(i==5)-int(i==4))for i in range(10)],[F(int(i==0)-int(i==9))for i in range(10)]]; capcenters=[th[5]-th[4]+2*(fr.pi[0]+fr.pi[1])/2-(fr.L[0]+fr.L[1])/2,th[0]-th[9]-(fr.L[0]+fr.L[1])/2]
B=np.vstack([np.eye(9),-np.ones(9)]);H0=np.array(jet['Hjet'])+float(penalty)*np.array(caps,float).T@np.array(caps,float);W=B@np.linalg.inv(np.linalg.cholesky(B.T@(H0-float(kappa)*np.eye(10))@B)).T
# Exactsumzero afterrationalization.
V=[[F(format(W[i,j],'.17g'))for j in range(9)]for i in range(9)];V.append([-sum(V[i][j]for i in range(9))for j in range(9)])
def interval(a,b):return I(I(a).lo,I(b).hi,True)
def trig(t):
 sn,cs=sc(abs(t));sn=(-sn[1],-sn[0])if t<0 else sn
 return [interval(*cs),interval(*sn)]
Ac=[trig(t)for t in th];AA=[[x+interval(-eps,eps)for x in a]for a in Ac]
ZZ=[[I(z0[e][k])+interval(-eps*sum(map(abs,T[e][k])),eps*sum(map(abs,T[e][k])))for k in range(2)]for e in range(40)]
TT=[[[sum(T[e][k][i]*V[i][j]for i in range(10))for j in range(9)]for k in range(2)]for e in range(40)]
H=[[I(-kappa*sum(V[k][i]*V[k][j]for k in range(10)))for j in range(9)]for i in range(9)]
for cap in caps:
 cv=[sum(cap[k]*V[k][i]for k in range(10))for i in range(9)]
 for i in range(9):
  for j in range(9):H[i][j]+=penalty*cv[i]*cv[j]
f0=I(0);grad=[I(0)for _ in range(10)];minnorm=1
for e in range(40):
 z=ZZ[e];norm=(z[0]*z[0]+z[1]*z[1]).sqrt();minnorm=min(minnorm,norm.lo/S);zz=[I(x)for x in z0[e]];nn=(zz[0]*zz[0]+zz[1]*zz[1]).sqrt();f0-=U*nn
 for i in range(10):grad[i]-=U*sum(zz[k]*T[e][k][i]for k in range(2))/nn
 # norm Hessian in 2D = outer(Jz,Jz)/|z|^3; preserves cancellation in directions.
 cross=[-z[1]*TT[e][0][i]+z[0]*TT[e][1][i]for i in range(9)]
 for i in range(9):
  for j in range(9):H[i][j]-=U*cross[i]*cross[j]/(norm*norm*norm)
 old=jet['edges'][e]
 if old>=24:
  a=(old-24)//2;AAe=AA[a];der=[AAe[1],-AAe[0]];d2=sum(AAe[k]*z[k]for k in range(2));mix=[sum(der[k]*TT[e][k][i]for k in range(2))for i in range(9)]
  for i in range(9):
   for j in range(9):H[i][j]+=V[a][i]*V[a][j]*d2+V[a][i]*mix[j]+V[a][j]*mix[i]
  f0-=sum(Ac[a][k]*zz[k]for k in range(2))
  for i in range(10):grad[i]-=sum(Ac[a][k]*T[e][k][i]for k in range(2))
  grad[a]+=Ac[a][1]*zz[0]-Ac[a][0]*zz[1]
for cap,b0 in zip(caps,capcenters):
 f0+=penalty*b0*b0/2
 for i in range(10):grad[i]+=penalty*b0*cap[i]
err=[[max(abs(H[i][j].lo-int(i==j)*S),abs(H[i][j].hi-int(i==j)*S))for j in range(9)]for i in range(9)]
bound=F(max(sum(row)for row in err),S)
out=dict(status='certified_hessian'if bound<1 else'inconclusive_width',scope='F(theta)=sum offset.z(theta)-U sum normz, exactbalancedaffineflow, |theta-th0|inf<=eps, sum(theta-th0)=0',penalty=str(penalty),caps=[[str(x)for x in cap]for cap in caps],capcenters=list(map(str,capcenters)),epsilon=str(eps),kappa=str(kappa),row_bound=str(bound),row_bound_display=float(bound),min_norm_lower_display=minnorm,f0=f0.dec(),gradient=[g.dec()for g in grad],theta0=list(map(str,th)),flow=[[str(x)for x in z]for z in z0],jet=[[[str(x)for x in row]for row in t]for t in T],V=[[str(x)for x in row]for row in V],H_intervals=[[x.dec()for x in row]for row in H])
(P/'q10-adaptive-penalty-interval.json').write_text(json.dumps(out,indent=2));print({k:v for k,v in out.items()if k in['status','epsilon','kappa','row_bound','min_norm_lower_display','f0']})

