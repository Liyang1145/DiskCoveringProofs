"""Family maxima ONLY; conditional C873 endpoints+C876 exactTcoincidence."""
from face_legal_arc_jet import bound as raw,objective,legal
from interval_joint_patch import I,pi
from patch_smooth_jet import Unsafe
L=I('.60946080763725372899')
def bound(box,j,side,cut):
 if not legal(box,j,side,cut):return None
 T=box[1]+box[2]
 # C876 covers entire exact coincidence and a collar; do not differentiate there.
 if T.a >= (pi/2-I('.005')).b and T.b <= (pi/2+I('.005')).a:return None
 try:
  f=objective(box,j,side,cut)
  if f.d[3].a>0 or f.d[3].b<0:return None
  if T.b<(pi/2).a or T.a>(pi/2).b:
   for k in [1,2]:
    if f.d[k].a>0 and box[k].b<1:return None
    if f.d[k].b<0 and box[k].a>L.b:return None
 except Unsafe:pass
 return raw(box,j,side,cut)
