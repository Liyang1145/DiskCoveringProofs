"""Driver for the 23 remaining v3 OPEN nodes: outer FORCE slabs (bnb) then LOCAL-SLAB energy (certA) per target.
Resumable; usage: open23.py <budget_s> [targets...]. Proposal + checker-A side only."""
import os as _os, sys as _sys  # hark-archive portable paths (see hark-archive/_paths.py)
_hd = _os.path.dirname(_os.path.abspath(__file__))
while _os.path.basename(_hd) != 'hark-archive' and _os.path.dirname(_hd) != _hd: _hd = _os.path.dirname(_hd)
_sys.path.append(_hd); from _paths import DCP_N26
import sys,os,json,time
sys.path.insert(0,DCP_N26+'/local'); sys.path.insert(0,DCP_N26)
sys.path.insert(0,DCP_N26+'/v3replay')
import warnings; warnings.filterwarnings('ignore')
from fractions import Fraction as F
import bnb, lgeom, prop, shgeom
from run_local import piece, OUT
LED=DCP_N26+'/ledger.jsonl'
T0=time.time(); BUD=float(sys.argv[1]); ts=sys.argv[2:] or lgeom.OPEN23
def left(): return BUD-(time.time()-T0)
for t in ts:
    tr,sl=lgeom.tree(t); os.makedirs(f'{OUT}/{t}',exist_ok=True); os.makedirs('fleaves',exist_ok=True)
    nf=nl=0; bad=[]
    for n,(m,lo,hi) in enumerate(sl):
        if m<0:
            p=f'fleaves/{t}_s{n}.json'
            if os.path.exists(p) and json.load(open(p))['done']: nf+=1; continue
            if left()<8: print(json.dumps({'stop':t,'phase':'outer','slab':n})); sys.exit(0)
            r=bnb.run(t,left()-3,path=p,box=(lo,hi)); r['slab']=n
            with open(LED,'a') as f: f.write(json.dumps({'event':'v3-open23-outer-force',**r,'t':time.time()})+'\n')
            if not r['done']: print(json.dumps({'stop':t,'phase':'outer','slab':n,'pending':r['pending']})); sys.exit(0)
            nf+=1
        else:
            fn=f'{OUT}/{t}/s{n}.json'
            if not os.path.exists(fn):
                sh=shgeom.map_slab(m,lo,hi)
                if sh is not None:
                    shf=f'{OUT}/shared/m{m}_s{sh}.json'
                    if not os.path.exists(shf): bad.append(('shared-missing',n,m,sh))
                    elif not json.load(open(shf))['closed']: bad.append(('shared-open',n,m,sh))
                    nl+=1; continue
            if os.path.exists(fn):
                nl+=1
                if not json.load(open(fn))['closed']: bad.append(n)
                continue
            if left()<8: print(json.dumps({'stop':t,'phase':'local','slab':n,'of':len(sl)})); sys.exit(0)
            rho=lgeom.RHO0/2**m
            b1,b2=prop.brange(lo,hi); K=int((b2-b1)/(F(3,10)*rho))+1
            acc=[]; ok=True
            for k in range(K): ok&=piece(lo,hi,b1+(b2-b1)*k/K,b1+(b2-b1)*(k+1)/K,0,acc)
            mb=min((F(p['bound']) for p in acc if 'bound' in p),default=None)
            rec={'target':t,'slab':n,'m':m,'lower':[str(x) for x in lo],'upper':[str(x) for x in hi],'b_range':[str(b1),str(b2)],
                 'mu':str(prop.MU),'closed':ok,'pieces':acc,'min_bound':str(mb),
                 'min_bound_over_rho2':float(mb/rho**2) if mb is not None else None}
            json.dump(rec,open(fn+'.tmp','w')); os.replace(fn+'.tmp',fn); nl+=1
            if not ok: bad.append(n)
            with open(LED,'a') as f: f.write(json.dumps({'event':'v3-open23-local-A','t':time.time(),'target':t,'slab':n,'m':m,'pieces':len(acc),'closed':ok,'min_b_rho2':rec['min_bound_over_rho2']})+'\n')
    print(json.dumps({'target':t,'A_side_done':True,'outer':nf,'local':nl,'local_not_closed':bad}))
print('ALL DONE')
