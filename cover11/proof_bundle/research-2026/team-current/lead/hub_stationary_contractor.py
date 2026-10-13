"""Parameterized Krawczyk enclosure, necessary for roots; no uniqueness assertion."""
import numpy as np
from hub_stationary_jet import gradient,Unsafe
from interval_joint_patch import I,lf,uf

def contract(box):
 x=[I(l,u)for l,u in box]
 mid=[I((l+u)/2)for l,u in box]
 try:
  jm=gradient(mid);M=np.array([[float(a.d[i].mid)for i in [3,4]]for a in jm]);C=np.linalg.inv(M)
  if not np.all(np.isfinite(C)) or np.max(abs(C))>1e5:return box
  js=gradient(x);bm=x[:3]+mid[3:];gm=gradient(bm)
  # C is any fixed finite matrix; its approximate inverse quality has no bearing on validity.
  out=box.copy()
  for i in range(2):
   val=mid[3+i]-sum((I(float(C[i,j]))*gm[j].v for j in range(2)),I(0))
   for k in range(2):
    fac=I(int(i==k))-sum((I(float(C[i,j]))*js[j].d[3+k]for j in range(2)),I(0))
    val+=fac*(x[3+k]-mid[3+k])
   lo=max(box[3+i][0],lf(val));hi=min(box[3+i][1],uf(val))
   if lo>hi:return None
   out[3+i]=(lo,hi)
  return out
 except (Unsafe,np.linalg.LinAlgError,ValueError):return box
