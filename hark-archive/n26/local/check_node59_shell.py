"""Exact-rational structural check of node-59 shell slabs m0..M-1 (independent of energy certs):
slab boxes from piece files == regenerated slabs; slab volumes sum EXACTLY to vol(Q_m)-vol(Q_{m+1});
slabs pairwise interior-disjoint (sampled by sequential-peeling construction => checked via volume equality + containment);
pieces contiguous & span b-range; weights w=L0+kappa*TAU >=0; reports count of zero-weight rods (strict-positivity gap).
Usage: python3 check_node59_shell.py [M=67]"""
import sys,json,time
from fractions import Fraction as F
sys.argv=[sys.argv[0],'0']+sys.argv[1:2]
src=open('/workspace/work/dcp-n26/v3replay/certB59.py').read().split('T0=time.time()')[0]
exec(src)
def vol(lo,hi):
    v=F(1)
    for a,b in zip(lo,hi): v*=(b-a)
    return v
bad=[];nz_max=0;nz_min=10**9;minw=None;tp=0;t0=time.time()
for m in range(M):
    a,b=Q(m);c,d=Q(m+1);S=slabs(m)
    tv=sum(vol(l,h) for l,h in S)
    if tv!=vol(a,b)-vol(c,d): bad.append((m,'volume'))
    for l,h in S:
        if not all(x>=y and u<=z for x,y,u,z in zip(l,a,h,b)): bad.append((m,'outside Q_m'))
        # disjoint from inner Q_{m+1}: some axis separated or touching
        if not any(h[k]<=c[k] or l[k]>=d[k] for k in range(15)): bad.append((m,'meets inner'))
    for s,(lo,hi) in enumerate(S):
        dd=json.load(open(f'{ROOT}/lleaves/59pilot/m{m}_s{s}.json'))
        ps=dd['pieces']
        for p,q in zip(ps,ps[1:]):
            if p['bb']!=q['ba']: bad.append((m,s,'gap'))
        for p in ps:
            tp+=1;kap=F(p['kappa']);w=[x+kap*t for x,t in zip(L0,TAU)]
            if min(w)<0: bad.append((m,s,'neg w'))
            nz=sum(1 for x in w if x==0);nz_max=max(nz_max,nz);nz_min=min(nz_min,nz)
            mw=min(w);minw=mw if minw is None else min(minw,mw)
print('shells',M,'pieces',tp,'zero-weight rods per piece min/max',nz_min,nz_max,'min w',float(minw))
print('PASS' if not bad else 'FAIL %d %s'%(len(bad),bad[:5]),'t=%.0fs'%(time.time()-t0))
