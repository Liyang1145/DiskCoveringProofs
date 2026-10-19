import os as _os, sys as _sys  # hark-archive portable paths (see hark-archive/_paths.py)
_hd = _os.path.dirname(_os.path.abspath(__file__))
while _os.path.basename(_hd) != 'hark-archive' and _os.path.dirname(_hd) != _hd: _hd = _os.path.dirname(_hd)
_sys.path.append(_hd); from _paths import DCP_MAIN_REPO
import sys, json, os, time
from fractions import Fraction as F
SRC=DCP_MAIN_REPO+'/cover26/proof_bundle/outputs/n26-sharp-candidate-angles-published-replay-v1'
sys.path.insert(0,SRC)
from n26_force import angular_domain, rootbox, tighten, load_trig
from n26_direct_arc_force import force_check
RUP=F("0.234700090400448239616790133776692127560495963654971391785925")
P=json.load(open(DCP_MAIN_REPO+'/cover26/proof_bundle/work/n26-sharp-candidate-angles-proposal-v3.json'))
spec=P['spec']; nodes=P['nodes']
arcs=load_trig()[0]
mat=angular_domain(spec)
lo,hi=rootbox(mat)
stack=[(0,lo,hi)]; boxes={}; res={}
t0=time.time(); minm=None
check_force = len(sys.argv)>1
while stack:
    i,lo,hi=stack.pop(); n=nodes[i]
    b=tighten(mat,lo,hi)
    if n['kind']=='EMPTY': assert b is None; continue
    assert b is not None
    lo,hi=b
    if n['kind']=='SPLIT':
        a=n['axis']; m=F(n['mid']); assert lo[a]<m<hi[a]
        lu=list(hi); lu[a]=m; rl=list(lo); rl[a]=m
        stack.append((n['children'][1],rl,list(hi))); stack.append((n['children'][0],list(lo),lu)); continue
    boxes[i]={'kind':n['kind'],'lo':[str(x) for x in lo],'hi':[str(x) for x in hi]}
    if n['kind']=='FORCE' and check_force:
        r=force_check(spec,lo,hi,n['cert'],arcs); m=F(r['required_radius_lower'])-RUP
        boxes[i]['margin']=float(m); minm=m if minm is None else min(minm,m)
json.dump({'boxes':boxes,'min_force_margin':float(minm) if minm is not None else None,'mat':mat},open('boxes.json.tmp','w'))
os.replace('boxes.json.tmp','boxes.json')
from collections import Counter
print(Counter(v['kind'] for v in boxes.values()), 'minmargin',minm and float(minm), 'neg', [k for k,v in boxes.items() if v.get('margin',1)<=0], time.time()-t0)
