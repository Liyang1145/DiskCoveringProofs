import os as _os, sys as _sys  # hark-archive portable paths (see hark-archive/_paths.py)
_hd = _os.path.dirname(_os.path.abspath(__file__))
while _os.path.basename(_hd) != 'hark-archive' and _os.path.dirname(_hd) != _hd: _hd = _os.path.dirname(_hd)
_sys.path.append(_hd); from _paths import DCP_MAIN_REPO
import sys,json
sys.path.insert(0,DCP_MAIN_REPO+'/cover26/proof_bundle/outputs/n26-sharp-candidate-angles-published-replay-v1')
from n26_force import angular_domain,tighten
import lgeom
P=json.load(open(DCP_MAIN_REPO+'/cover26/proof_bundle/work/n26-sharp-candidate-angles-proposal-v3.json'))
mat=angular_domain(P['spec'])
for t in sys.argv[1:]:
    tr,sl=lgeom.tree(t); bad=0
    def walk(n,lo,hi):
        global bad
        b=tighten(mat,lo,hi)
        if b is None or (list(b[0]),list(b[1]))!=(list(lo),list(hi)): bad+=1
        if n['kind']=='SPLIT':
            from fractions import Fraction as F
            k=n['axis'];m=F(n['mid']); h1=list(hi);h1[k]=m;l2=list(lo);l2[k]=m
            assert lo[k]<m<hi[k]
            walk(n['children'][0],lo,h1);walk(n['children'][1],l2,hi)
    walk(tr,*lgeom.T(t)); print(t,'nodes changed by tighten:',bad)
