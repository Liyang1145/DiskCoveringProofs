from low_family_maximum import bound as base,rd,bd
from low_family_second import objective,Unsafe
from interval_joint_patch import I,iv,uf

def bound(box,j):
 res=base(box,j)
 if res[1] is None or res[1]<28.10695:return res
 T=box[1]+box[2]
 # On coincidence only tangent directions and p are valid; base handles tangent first order.
 if j<2 and not(T.b<iv.pi.a/2 or T.a>iv.pi.b/2):return res
 for k in [1,2]:
  direction=[0]*4;direction[k]=1
  try:
   f=objective(box,j,direction);mid=box.copy();mid[k]=I((float(box[k].a)+float(box[k].b))/2);fm=objective(mid,j,direction);gd=fm.d+f.h*(box[k]-mid[k])
   if gd.a>0 and box[k].b<bd[1]:return 'familygradient',None
   if gd.b<0 and box[k].a>bd[0]:return 'familygradient',None
   if box[k].a>bd[0] and box[k].b<bd[1]:
    if f.h.a>0:return 'positivecurvature',None
    # At fullfamily maximum this bearing derivative=0; valid bound on those maxima only.
    up=uf(fm.v-f.h*(box[k]-mid[k])**2/2)
    res=(res[0],min(res[1],up))
    if up<28.10695:return res
  except Unsafe:pass
 return res
