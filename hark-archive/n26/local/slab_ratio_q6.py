import os as _os, sys as _sys  # hark-archive portable paths (see hark-archive/_paths.py)
_hd = _os.path.dirname(_os.path.abspath(__file__))
while _os.path.basename(_hd) != 'hark-archive' and _os.path.dirname(_hd) != _hd: _hd = _os.path.dirname(_hd)
_sys.path.append(_hd); from _paths import DCP_N26
import json
d=json.load(open(DCP_N26+'/local/FOREST-Q6.json'))
r=sorted((float(s['min_bound_over_rho2']),s['m'],s['slab']) for s in d['slabs'])
out={'n':len(r),'lowest10':r[:10],'median':r[len(r)//2],'frac_below_0.01':sum(x[0]<0.01 for x in r)/len(r),'pieces_keys':sorted(d['slabs'][0]['pieces'][0].keys())}
json.dump(out,open('slab_ratio_q6.json','w'));print(out)
