"""C872 eliminates both widths; C871 leaves three boundary charts."""
import allbearing_boundary_jet as hub
from width_endpoint_jet import endpoint
from patch_smooth_jet import Jet,Unsafe,asin
from interval_joint_patch import I,iv,z,pi,uf

def objective(box,j):
 r,b1,b2,p=[Jet(v,[I(int(i==k))for k in range(7)])for i,v in enumerate(box)]
 f=hub.objective(box,j)+endpoint(r,b1,0)+endpoint(r,b2,1)
 return f+Jet(pi*(z[113]+z[114]-z[2])+pi/2*(z[112]+z[115]-z[1]-z[3]))+Jet(1-z[1]-z[3])*asin(r)

def bound(box,j):
 if not hub.legal(box,j):return None
 try:
  f=objective(box,j);mid=[I((float(v.a)+float(v.b))/2)for v in box];fc=objective(mid,j)
  mv=fc.v+sum((d*(x-m)for d,x,m in zip(f.d,box,mid)),I(0))
  return min(uf(f.v),uf(mv)),[uf(abs(d))for d in f.d[:4]]
 except Unsafe:return float('inf'),[1]*4
