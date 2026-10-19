import json, sys
from fractions import Fraction as F
import verify_certs as V
import certify_box as cb
C=json.load(open('certs/1669.json')); B=V.PEND[1669]; den=C['weight_den']
out=[]
def rec(t,lo,hi):
    if t['kind']=='SPLIT':
        ax=t['axis']; m=F(t['mid']); h1=list(hi);h1[ax]=m; l2=list(lo); l2[ax]=m
        rec(t['children'][0],lo,h1); rec(t['children'][1],l2,hi); return
    if t['kind']!='LEAF': return
    out.append((t,lo,hi))
rec(C['tree'],[F(x) for x in B['lower']],[F(x) for x in B['upper']])
k=0
for t,lo,hi in out[::-1]:
    w=[F(x,den) for x in t['w']]; pairs=V.schur_kron(w); W=sum(w,F(0))
    b=V.leaf_bound(pairs,W,lo,hi)
    if b is None or b<=0:
        p2,W2=cb.exact_pairs(w); b2,_=cb.box_bound(p2,W2,lo,hi)
        same = (p2==pairs)
        print('fail: verifier',None if b is None else float(b/W),'prover',float(b2/W2),'claimed',t['margin_over_W'][:12],'pairs equal',same, 'width', float(max(h-l for l,h in zip(lo,hi))),flush=True)
        k+=1
        if k>=3: break
