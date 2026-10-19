"""Chunked driver (<=100 s per call, resumable): certify every shell slab of R with checker A."""
import json, os, sys, time
from fractions import Fraction as F
import geom, prop, certA
T0=time.time(); BUD=float(sys.argv[1]) if len(sys.argv)>1 else 100
OUT='/workspace/work/dcp-n26/local/leaves'
def piece(lo,hi,ba,bb,depth,acc):
    kap=(ba+bb)/2/prop.AA
    bd,_=certA.leaf_bound(prop.weight(kap),lo,hi,prop.V,ba,bb,prop.MU)
    if bd is not None and bd>0:
        acc.append({'ba':str(ba),'bb':str(bb),'kappa':str(kap),'bound':str(bd)}); return True
    if depth>=5: acc.append({'ba':str(ba),'bb':str(bb),'OPEN':True}); return False
    mid=(ba+bb)/2
    return piece(lo,hi,ba,mid,depth+1,acc) & piece(lo,hi,mid,bb,depth+1,acc)
done=0
for m in range(geom.mmax()):
    rho=geom.RHO0/2**m
    for si,(lo,hi) in enumerate(geom.slabs(m)):
        fn=f'{OUT}/m{m}_s{si}.json'
        if os.path.exists(fn): continue
        if time.time()-T0>BUD-12: print('budget stop, done',done); sys.exit(0)
        b1,b2=prop.brange(lo,hi); K=int((b2-b1)/(F(3,10)*rho))+1
        acc=[]; ok=True
        for k in range(K):
            ok&=piece(lo,hi,b1+(b2-b1)*k/K,b1+(b2-b1)*(k+1)/K,0,acc)
        rec={'m':m,'slab':si,'lower':[str(x) for x in lo],'upper':[str(x) for x in hi],'b_range':[str(b1),str(b2)],
             'mu':str(prop.MU),'closed':ok,'pieces':acc,'min_bound_over_rho2':min(float(F(p['bound'])/rho**2) for p in acc if 'bound' in p)}
        json.dump(rec,open(fn+'.tmp','w')); os.replace(fn+'.tmp',fn); done+=1
        with open('/workspace/work/dcp-n26/local/ledger.jsonl','a') as f:
            f.write(json.dumps({'t':time.time(),'m':m,'slab':si,'pieces':len(acc),'closed':ok,'min_b_rho2':rec['min_bound_over_rho2']})+'\n')
print('ALL DONE' ,done)
