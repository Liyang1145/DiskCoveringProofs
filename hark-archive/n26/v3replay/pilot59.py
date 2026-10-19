"""Pilot: local slab energy certs on shells of LOCAL cube 59 around theta* (inner cube stays LOCAL)."""
import sys,json,os,time
sys.path.insert(0,'/workspace/work/dcp-n26/local'); sys.path.insert(0,'/workspace/work/dcp-n26')
from fractions import Fraction as F
import prop, lgeom
from run_local import piece
B=json.load(open('boxes.json'))['boxes']['59']; LO=[F(x) for x in B['lo']]; HI=[F(x) for x in B['hi']]; C=lgeom.C
R0=max(max(c-l,h-c) for l,h,c in zip(LO,HI,C))
def Q(m):
    r=R0/2**m; return [max(l,c-r) for l,c in zip(LO,C)],[min(h,c+r) for h,c in zip(HI,C)]
def slabs(m):
    (lo,hi),(ilo,ihi)=Q(m),Q(m+1); lo=list(lo);hi=list(hi);out=[]
    for k in range(15):
        if lo[k]<ilo[k]: h=list(hi);h[k]=ilo[k];out.append((list(lo),h));lo[k]=ilo[k]
        if hi[k]>ihi[k]: l=list(lo);l[k]=ihi[k];out.append((l,list(hi)));hi[k]=ihi[k]
    return out
OUT='lleaves/59pilot'; os.makedirs(OUT,exist_ok=True)
T0=time.time(); BUD=float(sys.argv[1]); M=int(sys.argv[2])
for m in range(M):
    rho=R0/2**m
    for s,(lo,hi) in enumerate(slabs(m)):
        fn=f'{OUT}/m{m}_s{s}.json'
        if os.path.exists(fn): continue
        if time.time()-T0>BUD: print('budget stop'); sys.exit(0)
        b1,b2=prop.brange(lo,hi); K=int((b2-b1)/(F(3,10)*rho))+1; acc=[]; ok=True
        for k in range(K): ok&=piece(lo,hi,b1+(b2-b1)*k/K,b1+(b2-b1)*(k+1)/K,0,acc)
        mb=min((F(p['bound']) for p in acc if 'bound' in p),default=None)
        json.dump({'m':m,'slab':s,'rho':str(rho),'lower':[str(x) for x in lo],'upper':[str(x) for x in hi],'closed':ok,'pieces':acc,
                   'min_bound':str(mb),'min_bound_over_rho2':float(mb/rho**2) if mb else None},open(fn+'.tmp','w')); os.replace(fn+'.tmp',fn)
print('R0',float(R0),'done levels',M)
