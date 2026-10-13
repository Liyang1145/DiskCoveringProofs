"""Intersect naturalCartesianhub bounds with guarded full5variableMVT."""
import interval_cartesian_cancel as base
import interval_patch_delta as fibers
import cartesian_hub_jet as ad
from interval_joint_patch import I,uf
stats={'safe':0,'unsafe':0}
def setup(outer):
 st=base.setup(outer)
 if st is None:return None
 K,fs=st;raw,dom=fs[2]
 def hub(t):
  val=raw(t)
  if val is None:return None
  try:mv=ad.mean([*outer,t])
  except ad.Unsafe:stats['unsafe']+=1;return val
  stats['safe']+=1
  return I(max(val.a,mv.a),min(val.b,mv.b))
 return K,[*fs[:2],(hub,dom)]
def bound(outer,tol=1e-5,maxeval=31):
 st=setup(outer)
 if st is None:return None
 K,fs=st;rr=[fibers.envelope(fun,dom,tol,maxeval)for fun,dom in fs]
 if any(a['upper']==-float('inf')for a in rr):return None
 return {'upper':uf(K+sum((I(a['upper'])for a in rr),I(0))),'fibers':rr}
