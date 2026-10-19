"""Exact per-shell min piece bound and piece counts for FOREST-Q6 -> shell_min_q6.json"""
import json
from fractions import Fraction as F
d=json.load(open('/workspace/work/dcp-n26/local/FOREST-Q6.json'))
S={}
for s in d['slabs']:
    m=int(s['m']);mb=min(F(p['bound']) for p in s['pieces'])
    a=S.setdefault(m,[mb,0,0]);a[0]=min(a[0],mb);a[1]+=1;a[2]+=len(s['pieces'])
out={m:{'min_bound':float(v[0]),'min_bound_exact':str(v[0]),'slabs':v[1],'pieces':v[2],'ratio_x4m':float(v[0]*4**m)} for m,v in sorted(S.items())}
json.dump(out,open('/workspace/work/dcp-n26/local/shell_min_q6.json','w'),indent=1)
for m,v in out.items(): print(m,v['slabs'],v['pieces'],v['min_bound'],v['ratio_x4m'])
