"""Hubnormcircle boundary only; both polarroots retained, no maximizerclaimoutsideboundary."""
import interval_hub_saturated as base
import interval_patch_delta as fibers
from interval_joint_patch import I,uf

def bound(outer,tol=1e-5,maxeval=129):
 st=base.setup(outer)
 if st is None:return None
 K,ws,cs=st;ww=[fibers.envelope(fun,dom,tol,maxeval)for fun,dom in ws];cc=[fibers.envelope(fun,dom,tol,maxeval)for fun,dom in cs[2:]]
 if any(row['upper']==-float('inf')for row in ww)or all(row['upper']==-float('inf')for row in cc):return None
 total=K+sum((I(row['upper'])for row in ww),I(0))+I(max(row['upper']for row in cc))
 return {'upper':uf(total),'widths':ww,'normbranches':cc}
