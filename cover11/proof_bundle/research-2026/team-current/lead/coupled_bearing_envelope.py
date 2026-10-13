"""Bearing MVT preserves width/hub gradient cancellation with scalar width fibers."""
import allbearing_boundary_jet as hub
from joint_boundary_jet import width
from patch_smooth_jet import Jet,Unsafe
from interval_joint_patch import I,iv,pi,R,z,asin,acos,g,lf,uf
from interval_patch_delta import envelope

def bound(box,j,budget=33):
 if not hub.legal(box,j):return None
 r,b1,b2,p=box;bm=[I((float(b.a)+float(b.b))/2)for b in [b1,b2]]
 try:
  hh=hub.objective(box,j);hc=hub.objective([r,*bm,p],j)
 except Unsafe:return float('inf')
 K=pi*(z[113]+z[114]-z[2])+pi/2*(z[112]+z[115]-z[1]-z[3])+(1-z[1]-z[3])*asin(r)
 vals=[]
 for i,b in enumerate([b1,b2]):
  X=-r*iv.cos(2*b+asin(r));D=1-r*iv.sin(2*b+asin(r))
  if X.b<0:return None
  W=2*iv.atan2(I(max(I(0).a,X.a),X.b),D);lo=lf(g);hi=min(uf(2*asin(r)),uf(W))
  if lo>hi:return None
  def wf(w):
   try:
    rr=Jet(r);bb=Jet(b,[I(int(k==0))for k in range(7)]);ww=Jet(w)
    f,q=width(rr,bb,ww,i)
    if (q.v-r*r).a>0 or (q.v-(R*I('.19'))**2).b<0:return None
    fc,_=width(rr,Jet(bm[i]),ww,i)
    return fc.v+(f.d[0]+hh.d[i+1])*(b-bm[i])
   except Unsafe:return I('-inf','inf')
  v=envelope(wf,(lo,hi),.00005,budget)
  if v['upper']==-float('inf'):return None
  vals.append(v['upper'])
 return uf(K+hc.v+sum((I(v)for v in vals),I(0)))
