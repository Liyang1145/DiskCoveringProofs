"""Stationary-only Taylor, full coupled width endpoint objective."""
from all_boundary_derivative import derivative,enclosure
from low_low_boundary_jet import objective
import allbearing_boundary_jet as hub
from patch_smooth_jet import Unsafe
from interval_joint_patch import I,uf

def bound(box,j):
 if not hub.legal(box,j):return 'illegal',None
 up=float('inf')
 try:
  from interval_joint_patch import iv
  from legal_cartesian_value import value
  r,b1,b2,p=box
  if j<2:
   H=2*r*iv.sin(2*b1-p)if j==0 else 2*r*iv.sin(2*b2+p);v=H*iv.cos(p);t=H*iv.sin(p)
  else:v=iv.sqrt(1-r*r)+(1-r)*iv.cos(p);t=(1-r)*iv.sin(p)
  val=value(r,b1,b2,v,t)
  if val is None:return 'illegal',None
  up=uf(val)
  if up<28.10695:return 'value',up
 except Unsafe:pass
 try:
  der=enclosure(box,j)
  if der.a>0 or der.b<0:return 'nonstationary',None
  d=derivative(box,j);curv=d.d[3]
  if curv.a>0:return 'positivecurvature',None
  x=box.copy();x[3]=I((float(box[3].a)+float(box[3].b))/2)
  f=objective(x,j);mid=[I((float(v.a)+float(v.b))/2)for v in x];fm=objective(mid,j);mv=fm.v+sum((a*(v-m)for a,v,m in zip(f.d,x,mid)),I(0))
  upper=min(uf(f.v),uf(mv));tay=I(upper)-curv*(box[3]-x[3])**2/2
  return 'value',min(up,uf(tay))
 except Unsafe:return 'value',up
