import os as _os, sys as _sys  # hark-archive portable paths (see hark-archive/_paths.py)
_hd = _os.path.dirname(_os.path.abspath(__file__))
while _os.path.basename(_hd) != 'hark-archive' and _os.path.dirname(_hd) != _hd: _hd = _os.path.dirname(_hd)
_sys.path.append(_hd); from _paths import DCP_N26
import os,json
r=DCP_N26+'/v3replay/lleaves'
out={d:len([f for f in os.listdir(os.path.join(r,d)) if f.startswith('s') and f.endswith('.json')]) for d in sorted(os.listdir(r)) if os.path.isdir(os.path.join(r,d))}
json.dump(out,open(DCP_N26+'/local/count_lleaves.json','w'),indent=0)
print(sum(out.values()),len(out))
