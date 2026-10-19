"""Exact-rational margin table for FOREST-Q6: per shell m, min piece bound, bound/rho_m^2, rho_m=rho_0/2^m.
Gives the relative epsilon budget available for strict-positive-weight perturbation (needs bound/rho^2 > eps*Emax)."""
import json
from fractions import Fraction as F
d=json.load(open('/workspace/work/dcp-n26/local/FOREST-Q6.json'))
print({k:(v if not isinstance(v,(list,dict)) or len(str(v))<200 else '...') for k,v in d['shells'].items()} if isinstance(d['shells'],dict) else str(d['shells'])[:300])
mn={}
for s in d['slabs']:
    for p in s['pieces']:
        b=F(p['bound']); mn[s['m']]=min(mn.get(s['m'],b),b)
out={m:float(b) for m,b in sorted(mn.items())}
print(out)
json.dump(out,open('/workspace/work/dcp-n26/local/eps_budget_q6.json','w'))
