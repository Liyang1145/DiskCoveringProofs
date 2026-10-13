"""Independent Cartesian circleparametrization control for hubnormboundary."""
import interval_hub_boundary as base
import interval_patch_delta as fibers
from interval_joint_patch import I,uf

def bound(outer,tol=1e-5,maxeval=129):
 st=base.setup(outer)
 if st is None:return None
 K,ws,cs=st;ww=[fibers.envelope(fun,dom,tol,maxeval)for fun,dom in ws];fun,dom=cs[2];cc=fibers.envelope(fun,dom,tol,maxeval)
 if any(row['upper']==-float('inf')for row in ww)or cc['upper']==-float('inf'):return None
 return {'upper':uf(K+sum((I(row['upper'])for row in ww),I(0))+I(cc['upper']))}
