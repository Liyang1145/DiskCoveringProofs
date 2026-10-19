import os as _os, sys as _sys  # hark-archive portable paths (see hark-archive/_paths.py)
_hd = _os.path.dirname(_os.path.abspath(__file__))
while _os.path.basename(_hd) != 'hark-archive' and _os.path.dirname(_hd) != _hd: _hd = _os.path.dirname(_hd)
_sys.path.append(_hd); from _paths import DCP_N26
import json,os,sys
sys.argv=['x','0','67']
src=open(DCP_N26+'/v3replay/certB59.py').read().split('T0=time.time()')[0]
exec(src)
S=json.load(open(ROOT+'/verB59.json'))['done']
tot=[];miss=[]
for m in range(67):
    for s,_ in enumerate(slabs(m)):
        k=f'{m}_{s}';tot.append(k)
        if k not in S: miss.append(k)
print(len(tot),len(S),'missing',miss,'extra',[k for k in S if k not in tot][:10])
for k in miss:
    f=f'{ROOT}/lleaves/59pilot/{k.replace("_","_s").replace("m","m")}'
