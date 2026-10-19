"""Per top-level subtree: tree LOCAL-SLAB leaf count vs disk leaf files (gap list)."""
import os as _os, sys as _sys  # hark-archive portable paths (see hark-archive/_paths.py)
_hd = _os.path.dirname(_os.path.abspath(__file__))
while _os.path.basename(_hd) != 'hark-archive' and _os.path.dirname(_hd) != _hd: _hd = _os.path.dirname(_hd)
_sys.path.append(_hd); from _paths import DCP_N26
import json,collections
t=json.load(open(DCP_N26+'/v3replay/V3-REPLAY-TREE.json'));N=t['nodes']
cnt=json.load(open('count_lleaves.json'))
res={}
for r in N[0]['children'] if N[0]['kind']=='SPLIT' else []:
    c=collections.Counter();st=[r]
    while st:
        i=st.pop();x=N[i];c[x['kind']]+=1
        if x['kind']=='SPLIT':st+=x['children']
    res[r]={'LS':c['LOCAL-SLAB'],'disk':cnt.get(str(r),0),'nodes':sum(c.values())}
json.dump(res,open('gap_lleaves.json','w'),indent=0)
print(sum(v['LS'] for v in res.values()),sum(v['disk'] for v in res.values()))
for r,v in sorted(res.items(),key=lambda kv:kv[1]['LS']-kv[1]['disk'])[:15]:print(r,v)
