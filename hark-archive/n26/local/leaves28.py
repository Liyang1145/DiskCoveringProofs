"""Manifest of node-28 LOCAL-SLAB leaves from v3replay/lleaves/28/*.json (closed flag, m, min_bound/rho2, piece count). Exact Fractions."""
import json,glob,collections
from fractions import Fraction as F
R=[];c=collections.Counter()
for f in sorted(glob.glob('/workspace/work/dcp-n26/v3replay/lleaves/28/s*.json')):
    d=json.load(open(f));lo=[F(x) for x in d['lower']];up=[F(x) for x in d['upper']]
    assert all(a<b for a,b in zip(lo,up))
    mb=F(d['min_bound']);c[(d['closed'],d['m'])]+=1
    R.append({'slab':d['slab'],'m':d['m'],'closed':d['closed'],'pieces':len(d['pieces']),'min_bound_pos':mb>0,'ratio':d['min_bound_over_rho2'],'dim':len(lo)})
out={'n':len(R),'closed':sum(r['closed'] in (True,'True') for r in R),'all_min_bound_pos':all(r['min_bound_pos'] for r in R),'min_ratio':min(float(r['ratio']) for r in R),'pieces_total':sum(r['pieces'] for r in R),'by_closed_m':{f'{k[0]}|{k[1]}':v for k,v in c.items()},'leaves':R}
json.dump(out,open('leaves28.json','w'))
print({k:v for k,v in out.items() if k!='leaves'})
