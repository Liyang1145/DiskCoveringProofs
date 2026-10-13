"""Parameterized scalar interval-Newton contraction, necessary stationarity only."""
from all_boundary_derivative import derivative,enclosure
from low_stationary_bound import bound as raw
from patch_smooth_jet import Unsafe
from interval_joint_patch import I,lf,uf

def contract(box,j):
 for _ in range(2):
  try:
   d=derivative(box,j);curv=d.d[3]
   if curv.a<=0<=curv.b:return box
   mid=box.copy();mid[3]=I((float(box[3].a)+float(box[3].b))/2);gm=enclosure(mid,j)
   root=mid[3]-gm/curv;lo=max(box[3].a,root.a);hi=min(box[3].b,root.b)
   if lo>hi:return None
   if lo==box[3].a and hi==box[3].b:return box
   box=box.copy();box[3]=I(lo,hi)
  except Unsafe:return box
 return box

def bound(box,j):
 b=contract(box,j)
 if b is None:return 'nonstationary',None
 return raw(b,j)
