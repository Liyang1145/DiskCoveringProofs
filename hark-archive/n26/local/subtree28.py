"""Subtree census of replay-tree node 28 (root28): leaf kinds, depth, FORCE/LOCAL-SLAB counts, no OPEN."""
import os as _os, sys as _sys  # hark-archive portable paths (see hark-archive/_paths.py)
_hd = _os.path.dirname(_os.path.abspath(__file__))
while _os.path.basename(_hd) != 'hark-archive' and _os.path.dirname(_hd) != _hd: _hd = _os.path.dirname(_hd)
_sys.path.append(_hd); from _paths import DCP_N26
import json,collections,sys
t=json.load(open(DCP_N26+'/v3replay/V3-REPLAY-TREE.json'));N=t['nodes']
root=int(sys.argv[1]) if len(sys.argv)>1 else 28
c=collections.Counter();maxd=0;ax=collections.Counter();st=[(root,0)]
while st:
    i,d=st.pop();x=N[i];maxd=max(maxd,d);c[x['kind']]+=1
    if x['kind']=='SPLIT':
        ax[x['axis']]+=1;st+=[(k,d+1) for k in x['children']]
print(json.dumps({'root':root,'kinds':c,'maxdepth':maxd,'split_axes':ax},default=dict))
