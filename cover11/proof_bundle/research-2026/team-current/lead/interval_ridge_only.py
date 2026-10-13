"""Ridge subset only: exact hub value, independently maximized width fibers. No max-to-ridge premise."""
import interval_hub_boundary as base
import interval_patch_delta as fibers
from interval_joint_patch import I,iv,R,z,uf
import interval_joint_patch as k
def bound(outer,tol=.00015,maxeval=129):
 st=base.setup(outer)
 if st is None:return None
 K,ws,_=st;r,b1,b2=outer;d=b1-b2;H=2*r*iv.sin(b1+b2)
 hub=(z[3]-z[1])*d+4*r*r*iv.sin(b1+b2)*iv.sin(b1)*iv.sin(b2)+(z[1]-z[9])*b1+(z[3]-z[9])*b2
 hub+=k.quad_range(-z[16],-z[78],r*iv.sin(b2)/R)+k.quad_range(z[20],z[82],r*iv.sin(b1)/R)
 ww=[fibers.envelope(fun,dom,tol,maxeval)for fun,dom in ws]
 if any(a['upper']==-float('inf')for a in ww):return None
 return {'upper':uf(K+hub+sum((I(a['upper'])for a in ww),I(0))),'widths':ww}
