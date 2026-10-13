"""Numeric candidate calibration and exact rational layer identity controls, not continuum certification."""
from coupled_primal_probe import *
from fractions import Fraction as F
import random
if __name__=='__main__':
 c=[math.pi-t for t in x0[:ne]];internal=[];anchors=[]
 for k,e in enumerate(edges):
  fs=E[e]
  (internal if len(fs)==2 else anchors).append((fs,c[k]))
 bestlo=(1e10,None);besthi=(1e10,None)
 for mask in range(1,1<<nf):
  inside=lambda f: bool(mask&(1<<f));I0=sum(w for fs,w in internal if all(inside(f)for f in fs));B0=sum(w for fs,w in internal if sum(inside(f)for f in fs)==1)+sum(w for fs,w in anchors if inside(fs[0]));n=mask.bit_count();lo=math.pi*n-I0;hi=I0+B0-math.pi*n
  if lo<bestlo[0]:bestlo=(lo,mask)
  if hi<besthi[0]:besthi=(hi,mask)
 # Exact layer identity on artificial rational graph with same incidence, arbitrary signed logs.
 rng=random.Random(1259);rr=[([*fs],F(rng.randint(1,10),7))for fs,_ in internal];aa=[([*fs],F(rng.randint(1,10),7))for fs,_ in anchors];pi=F(22,7)
 for run in range(100):
  z=[F(rng.randint(-20,20),3)for _ in range(nf)];direct=pi*sum(z)-sum(w*min(z[f]for f in fs)for fs,w in rr)-sum(w*min(z[fs[0]],F(0))for fs,w in aa);layers=F(0)
  for sg in [1,-1]:
   levels=sorted(set([F(0)]+[sg*t for t in z if sg*t>0]))
   for t0,t1 in zip(levels,levels[1:]):
    S0={f for f,t in enumerate(z)if sg*t>(t0+t1)/2};Iv=sum(w for fs,w in rr if all(f in S0 for f in fs));Bv=sum(w for fs,w in rr if sum(f in S0 for f in fs)==1)+sum(w for fs,w in aa if fs[0]in S0);layers+=(t1-t0)*(pi*len(S0)-Iv if sg==1 else Iv+Bv-pi*len(S0))
  assert direct==layers
 out={'status':'numeric_candidate_cuts_and_exact_algebra_controls','nfaces':nf,'subsets':(1<<nf)-1,'min_lower_cut_margin':bestlo,'min_upper_cut_margin':besthi,'exact_rational_layer_controls':100};(P/'dirichlet-cut-control.json').write_text(json.dumps(out,indent=2));print(out)
