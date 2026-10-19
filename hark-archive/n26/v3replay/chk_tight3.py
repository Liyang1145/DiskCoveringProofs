import os as _os, sys as _sys  # hark-archive portable paths (see hark-archive/_paths.py)
_hd = _os.path.dirname(_os.path.abspath(__file__))
while _os.path.basename(_hd) != 'hark-archive' and _os.path.dirname(_hd) != _hd: _hd = _os.path.dirname(_hd)
_sys.path.append(_hd); from _paths import DCP_MAIN_REPO
import sys,json
from fractions import Fraction as F
sys.path.insert(0,DCP_MAIN_REPO+'/cover26/proof_bundle/outputs/n26-sharp-candidate-angles-published-replay-v1')
from n26_force import angular_domain,tighten
import lgeom
P=json.load(open(DCP_MAIN_REPO+'/cover26/proof_bundle/work/n26-sharp-candidate-angles-proposal-v3.json'))
mat=angular_domain(P['spec'])
for t in sys.argv[1:]:
  tr,sl=lgeom.tree(t)
  def walk(n,lo,hi):
    b=tighten(mat,lo,hi); assert b is not None
    lo2,hi2=b
    if n['kind']=='SPLIT':
        k=n['axis'];m=F(n['mid'])
        if not lo2[k]<m<hi2[k]: print('BAD split',k)
        h1=list(hi2);h1[k]=m;l2=list(lo2);l2[k]=m
        walk(n['children'][0],lo2,h1);walk(n['children'][1],l2,hi2)
    else:
        if (list(lo2),list(hi2))!=(list(lo),list(hi)): print(t,'slab',n['n'],'level',sl[n['n']][0],'tightened')
  walk(tr,*lgeom.T(t))
print('ok')
