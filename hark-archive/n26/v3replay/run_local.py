"""Checker-A driver: LOCAL-SLAB energy leaves for shell slabs (level>=0) of v3 boxes. Resumable, <=budget s."""
import sys, json, os, time
sys.path.insert(0,'/workspace/work/dcp-n26/local'); sys.path.insert(0,'/workspace/work/dcp-n26')
from fractions import Fraction as F
import lgeom, prop, certA
OUT='/workspace/work/dcp-n26/v3replay/lleaves'
def piece(lo,hi,ba,bb,depth,acc):
    kap=(ba+bb)/2/prop.AA
    bd,_=certA.leaf_bound(prop.weight(kap),lo,hi,prop.V,ba,bb,prop.MU)
    if bd is not None and bd>0:
        acc.append({'ba':str(ba),'bb':str(bb),'kappa':str(kap),'bound':str(bd)}); return True
    if depth>=5: acc.append({'ba':str(ba),'bb':str(bb),'OPEN':True}); return False
    mid=(ba+bb)/2
    return piece(lo,hi,ba,mid,depth+1,acc) & piece(lo,hi,mid,bb,depth+1,acc)
if __name__=='__main__':
    T0=time.time(); BUD=float(sys.argv[1]); ts=sys.argv[2:]
    done=0
    for t in ts:
        os.makedirs(f'{OUT}/{t}',exist_ok=True)
        tr,sl=lgeom.tree(t)
        for n,(m,lo,hi) in enumerate(sl):
            if m<0: continue
            fn=f'{OUT}/{t}/s{n}.json'
            if os.path.exists(fn): continue
            if time.time()-T0>BUD: print('budget stop',t,'done',done); sys.exit(0)
            rho=lgeom.RHO0/2**m
            b1,b2=prop.brange(lo,hi); K=int((b2-b1)/(F(3,10)*rho))+1
            acc=[]; ok=True
            for k in range(K): ok&=piece(lo,hi,b1+(b2-b1)*k/K,b1+(b2-b1)*(k+1)/K,0,acc)
            rec={'target':t,'slab':n,'m':m,'lower':[str(x) for x in lo],'upper':[str(x) for x in hi],'b_range':[str(b1),str(b2)],
                 'mu':str(prop.MU),'closed':ok,'pieces':acc,
                 'min_bound':min((F(p['bound']) for p in acc if 'bound' in p),default=None) }
            rec['min_bound_over_rho2']=float(rec['min_bound']/rho**2) if rec['min_bound'] is not None else None
            rec['min_bound']=str(rec['min_bound'])
            json.dump(rec,open(fn+'.tmp','w')); os.replace(fn+'.tmp',fn); done+=1
            with open('/workspace/work/dcp-n26/ledger.jsonl','a') as f:
                f.write(json.dumps({'event':'v3-local-A','t':time.time(),'target':t,'slab':n,'m':m,'pieces':len(acc),'closed':ok,'min_b_rho2':rec['min_bound_over_rho2']})+'\n')
    print('ALL DONE',ts,done)
