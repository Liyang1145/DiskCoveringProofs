"""Exclude family maxima, conditional on C873 endpoints. Never individual arc bound."""
from low_stationary_bound import bound as stationary
from low_low_boundary_jet import objective
from allbearing_boundary_jet import legal
from patch_smooth_jet import Unsafe
from interval_joint_patch import I,iv,lf,uf
rd=(lf(I('.379')),uf(I('.37999')));bd=(lf(I('.60946080763725372899')),1.)

def bound(box,j):
 if not legal(box,j):return 'illegal',None
 try:
  # Face coincidence contains extra active constraint and cannot use this test.
  T=box[1]+box[2]
  f=objective(box,j)
  keys=[(0,rd)]
  if j==2 or T.b<iv.pi.a/2 or T.a>iv.pi.b/2:keys += [(1,bd),(2,bd)]
  else:
   # Tangent to coincidence T=pi/2; also feasible at all inactive-face points.
   dg=f.d[1]-f.d[2]
   if dg.a>0 and box[1].b<bd[1] and box[2].a>bd[0]:return 'familygradient',None
   if dg.b<0 and box[1].a>bd[0] and box[2].b<bd[1]:return 'familygradient',None
  for k,dom in keys:
    if f.d[k].a>0 and box[k].b<dom[1]:return 'familygradient',None
    if f.d[k].b<0 and box[k].a>dom[0]:return 'familygradient',None
 except Unsafe:pass
 return stationary(box,j)
