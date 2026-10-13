"""Necessary disk residuals g<=0 yield upper majorants F-lambda*g, lambda>=0."""
from low_low_boundary_jet import objective
from patch_smooth_jet import Jet,Unsafe,sin,cos,sqrt
import allbearing_boundary_jet as hub
from interval_joint_patch import I,uf

def residuals(box,j):
 r,b1,b2,p=[Jet(v,[I(int(i==k))for k in range(7)])for i,v in enumerate(box)];s=sqrt(1-r*r)
 if j<2:
  H=2*r*sin(2*b1-p)if j==0 else 2*r*sin(2*b2+p);v=H*cos(p);t=H*sin(p)
 else:v=s+(1-r)*cos(p);t=(1-r)*sin(p)
 gs=[(v-r*sin(2*b1))**2+(t+r*cos(2*b1))**2-r*r,(v-r*sin(2*b2))**2+(t-r*cos(2*b2))**2-r*r,(v-s)**2+t*t-(1-r)**2]
 return gs

def bound(box,j):
 if not hub.legal(box,j):return None
 try:
  f=objective(box,j);gs=residuals(box,j);mid=[I((float(x.a)+float(x.b))/2)for x in box];fc=objective(mid,j);gc=residuals(mid,j)
  upper=float('inf');bestd=[1]*4
  multipliers=[(0,0,0)]
  for k in range(3):
   if k==j:continue
   for lam in ['.5','1.1','2']:
    row=[0,0,0];row[k]=lam;multipliers.append(row)
  for ll in multipliers:
   a=f-sum((Jet(I(l))*g for l,g in zip(ll,gs)),Jet(0));ac=fc-sum((Jet(I(l))*g for l,g in zip(ll,gc)),Jet(0));mv=ac.v+sum((d*(x-m)for d,x,m in zip(a.d,box,mid)),I(0));u=min(uf(a.v),uf(mv))
   if u<upper:upper=u;bestd=[uf(abs(d))for d in a.d[:4]]
  return upper,bestd
 except Unsafe:return float('inf'),[1]*4
