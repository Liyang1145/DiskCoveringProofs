"""Specialized outward distance-square bound with a proved absolute roundoff guard.
All interval endpoints binary64, absolute value≤2. Exact difference≤4.
Two correctly rounded subtractions each error≤2^-51; max with0 preserves
absolute error. For q∈[0,4], |fl(q)^2−q^2|≤8*2^-51+2^-102+2^-49.
Rounded summation of two squares adds≤2^-48 and the final subtraction
(or addition) of PAD adds≤2^-48. Even counting an extra2^-51 per
coordinate, total error≤2*(9*2^-51+2^-102+2^-49)+2*2^-48<2^-45.
We subtract/add2^-42 (larger exact dyadic) in final comparison bounds. No
transcendental calls; no directed-mode dependence. Input rational endpoints
still use audited exact Fraction→binary64 outward conversion.
"""
import hubline_atoms as A
import numpy as np,json,time,sys
from fractions import Fraction as F
PAD=2.0**-42
class FastAtoms(A.Atoms):
 def __init__(self,*args,**kw):
  super().__init__(*args,**kw)
  assert all(np.all(np.abs(v)<=2) for v in (*self.X,*self.Y))
 def bound(self,B):
  a,b,c,d=B
  assert max(abs(a),abs(b),abs(c),abs(d))<=2
  # Squared norm rectangle lower/upper; same absolute error bound applies.
  nearx=max(a,-b,0.);neary=max(c,-d,0.)
  farx=max(abs(a),abs(b));fary=max(abs(c),abs(d))
  low=nearx*nearx+neary*neary-PAD;high=farx*farx+fary*fary+PAD
  if high<self.inner[0] or low>self.outer[1]:return -1
  dx=np.maximum(np.maximum(self.X[0]-b,a-self.X[1]),0.)
  dy=np.maximum(np.maximum(self.Y[0]-d,c-self.Y[1]),0.)
  d2=dx*dx+dy*dy-PAD
  return int(self.W[d2<=self.r2[1]].sum())
if __name__=='__main__':
 eps=F(sys.argv[1]) if len(sys.argv)>1 else F(1,1000);N=int(sys.argv[2]) if len(sys.argv)>2 else 2048
 s=F(1,5);x=F(0);y=F(1,80);HB=[(s-eps,s+eps),(x,x+eps),(y-eps,y+eps)]
 source=json.loads((A.P/'evidence/hubline-point-0.json').read_text());W=source['proposal']['weights']
 t=time.time();C=FastAtoms(HB,W,N);out=C.certify();out.update({'seconds':time.time()-t,'H':[[str(v) for v in r] for r in HB],'N':N})
 print(json.dumps(out),flush=True);(A.P/'evidence'/('hubline-atoms-fast-'+str(eps).replace('/','-')+'.json')).write_text(json.dumps(out,indent=2))
