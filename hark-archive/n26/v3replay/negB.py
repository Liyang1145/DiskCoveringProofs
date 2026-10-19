import json,sys
from fractions import Fraction as F
import certB_v3 as CB
D=json.load(open('V3-REPLAY-TREE.json')); spec=D['spec']; nodes=D['nodes']
M=CB.domain(spec)
A=json.load(open('boxes.json'))
print('domain matrix equal to archive angular_domain:',M==A['mat'])
Bx=A['boxes']['59']; lo=[F(x) for x in Bx['lo']]; hi=[F(x) for x in Bx['hi']]
cache={}; worst=None
for i,n in enumerate(nodes):
    if n['kind']=='FORCE':
        L=CB.force_B(spec,lo,hi,n['cert'],cache)
        if L is not None and L>CB.RUP: print('NEG CONTROL FAILED',i)
        worst=L if worst is None or (L is not None and L>worst) else worst
print('best force bound on LOCAL box 59 minus RUP:',float(worst-CB.RUP))
c=dict(nodes[97]['cert']) if nodes[97]['kind']=='FORCE' else None
print('zero-g cert ->',CB.force_B(spec,[F(x) for x in A['boxes']['97']['lo']],[F(x) for x in A['boxes']['97']['hi']],{'g':[0]*30,'f':nodes[97]['cert']['f']},cache))
# LOCAL energy check on a slab containing theta*: use LOCAL box 59 with piece kappa from a real leaf
d=json.load(open('lleaves/135/s51.json')); x=d['pieces'][0]
kap=F(x['kappa']); w=[a+kap*t for a,t in zip(CB.LB.L0,CB.LB.TAU)]
V=[F(v) for v in json.load(open('/workspace/work/dcp-n26/local/prop.json'))['v']]
b1=sum(min(v*(a-c),v*(bb-c)) for v,a,bb,c in zip(V,lo,hi,CB.LB.CS)); b2=sum(max(v*(a-c),v*(bb-c)) for v,a,bb,c in zip(V,lo,hi,CB.LB.CS))
bd=CB.LB.check_leaf(w,lo,hi,b1,b2,F(d['mu']))
print('energy check on box 59 (contains theta*):',bd if bd is None else float(bd))
