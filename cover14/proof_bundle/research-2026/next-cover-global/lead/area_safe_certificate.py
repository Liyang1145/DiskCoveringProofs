"""Directed supporting-plane bounds for safe area-angle relaxation, no optimizer trust."""
import json,math,numpy as np
from itertools import combinations
from root_integer_certificate import I,Q,S
from pathlib import Path
P=Path(__file__).resolve().parent
U=Q('0.33173203427623414')
def atan(x,N=90):
 a=sum(((-1)**n*x**(2*n+1)/(2*n+1)for n in range(N)),Q(0));b=a+(-1)**N*x**(2*N+1)/(2*N+1)
 return I(I(min(a,b)).lo,I(max(a,b)).hi,True)
PI=16*atan(Q(1,5))-4*atan(Q(1,239))
def asin(x,N=100):
 a=sum((Q(math.comb(2*n,n),4**n*(2*n+1))*x**(2*n+1)for n in range(N)),Q(0));b=a+x**(2*N+1)/(1-x*x)
 return I(I(a).lo,I(b).hi,True)
L=2*asin(U)
def trig(x):
 # Taylor through degree80, remainder <=4^81/81! on|x|<=4.
 assert x.absmax()<=4*S
 sn=I(0);cs=I(0);term=I(1)
 for n in range(81):
  if n%2:sn+=(-1)**((n-1)//2)*term
  else:cs+=(-1)**(n//2)*term
  term=term*x/(n+1)
 err=I(Q(4**81,math.factorial(81)));ee=I(-err.hi,err.hi,True)
 return sn+ee,cs+ee
ss,cc=trig(I(0));assert ss.lo<=0<=ss.hi and cc.lo<=S<=cc.hi
ss,cc=trig(PI/2);assert ss.lo<=S<=ss.hi and cc.lo<=0<=cc.hi
# sinL=2U sqrt(1-U²), avoids extra transcendental call.
cap_minus_pi=-PI*(2*I(U)*(1-I(U)**2).sqrt())/L
def certify(n,q,edges,angles,idx=None):
 B=np.zeros((n,q+len(edges)))
 for i in range(q):B[i,i]=1
 for j,(u,v)in enumerate(edges):B[u,q+j]=1;B[v,q+j]=1
 aa=[U*U/2]*q+[U*U]*len(edges)
 t=[max(Q(0),min(Q('3.141592653589'),Q(format(float(x),'.12f'))))for x in angles]
 assert all(0<=x and I(x).hi<=PI.lo for x in t)
 grad=np.array([float(a)*math.cos(float(x))for a,x in zip(aa,t)])
 from scipy.optimize import linprog
 m=len(t)
 lp=linprog(np.r_[np.full(n,2.),np.ones(m)],A_ub=np.c_[-B.T,-np.eye(m)],b_ub=-grad,bounds=[(None,None)]*n+[(0,None)]*m,method='highs')
 assert lp.success
 y=[Q(format(x,'.12f'))for x in lp.x[:n]]
 bound=verify(n,q,edges,t,y)
 return {'index':idx,'status':'excluded'if bound.hi<0 else'inconclusive','area_minus_pi_enclosure':bound.dec(),'upper_display':bound.hi/S,'rational_angles':list(map(str,t)),'rational_node_potentials':list(map(str,y))}
def verify(n,q,edges,t,y):
 assert len(t)==q+len(edges) and len(y)==n
 assert all(0<=x and I(x).hi<=PI.lo for x in t)
 aa=[U*U/2]*q+[U*U]*len(edges)
 bound=cap_minus_pi+2*PI*sum(y)
 for j,(a,x)in enumerate(zip(aa,t)):
  sn,cs=trig(I(x));bound+=I(a)*(sn-I(x)*cs)
  potential=y[j]if j<q else sum(y[i]for i in edges[j-q])
  slope=I(a)*cs-potential
  bound+=PI*I(max(0,slope.lo),max(0,slope.hi),True)
 return bound
if __name__=='__main__':
 D=json.loads((P/'q11-pocket-catalogue.json').read_text());data=json.loads((P/'area-safe-probe.json').read_text());out=[]
 for run in data['runs']:
  idx=run['index'];edges=sorted({tuple(sorted(e))for f in D['entries'][idx]['faces']for e in combinations(f,2)})
  out.append(certify(14,11,edges,run['angles'],idx))
 (P/'area-safe-certificate.json').write_text(json.dumps({'status':'exact_interval_supporting_plane_bounds','scope':'12 specified q11 graph angle relaxations atU; geometric interface inAREA-SAFE-RELAXATION.md','threshold':str(U),'pi_enclosure':PI.dec(),'L_enclosure':L.dec(),'runs':out},indent=2))
 print([(x['index'],x['status'],x['upper_display'])for x in out])
