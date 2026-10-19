"""Checker-A side: certA LOCAL-SLAB energy certs on the shared annulus slabs (shgeom) needed by the OPEN23 targets.
Resumable; usage: run_shared.py <budget_s>"""
import sys,os,json,time
sys.path.insert(0,'/workspace/work/dcp-n26/v3replay'); sys.path.insert(0,'/workspace/work/dcp-n26/local')
from fractions import Fraction as F
import lgeom, shgeom, prop
from run_local import piece
OUT='/workspace/work/dcp-n26/v3replay/lleaves/shared'; os.makedirs(OUT,exist_ok=True)
NF=OUT+'/NEED.json'
if not os.path.exists(NF):
    need=set()
    for t in lgeom.OPEN23:
        if t=='1': continue
        tr,sl=lgeom.tree(t)
        for (m,lo,hi) in sl:
            if m<0: continue
            s=shgeom.map_slab(m,lo,hi)
            if s is not None: need.add((m,s))
    json.dump(sorted(need),open(NF+'.tmp','w')); os.replace(NF+'.tmp',NF)
need=json.load(open(NF)); T0=time.time(); BUD=float(sys.argv[1]); done=0; bad=[]
for m,s in need:
    fn=f'{OUT}/m{m}_s{s}.json'
    if os.path.exists(fn):
        if not json.load(open(fn))['closed']: bad.append((m,s))
        continue
    if time.time()-T0>BUD: print(json.dumps({'stop':True,'done_now':done,'have':len(os.listdir(OUT))-1,'need':len(need),'bad':bad})); sys.exit(0)
    lo,hi=shgeom.slabs(m)[s]; rho=lgeom.RHO0/2**m
    b1,b2=prop.brange(lo,hi); K=int((b2-b1)/(F(3,10)*rho))+1; acc=[]; ok=True
    for k in range(K): ok&=piece(lo,hi,b1+(b2-b1)*k/K,b1+(b2-b1)*(k+1)/K,0,acc)
    mb=min((F(p['bound']) for p in acc if 'bound' in p),default=None)
    rec={'target':'shared-annulus','m':m,'slab':s,'rho':str(rho),'lower':[str(x) for x in lo],'upper':[str(x) for x in hi],
         'b_range':[str(b1),str(b2)],'mu':str(prop.MU),'closed':ok,'pieces':acc,'min_bound':str(mb),
         'min_bound_over_rho2':float(mb/rho**2) if mb is not None else None}
    json.dump(rec,open(fn+'.tmp','w')); os.replace(fn+'.tmp',fn); done+=1
    if not ok: bad.append((m,s))
    with open('/workspace/work/dcp-n26/ledger.jsonl','a') as f:
        f.write(json.dumps({'event':'v3-shared-local-A','t':time.time(),'m':m,'slab':s,'pieces':len(acc),'closed':ok,'min_b_rho2':rec['min_bound_over_rho2']})+'\n')
print(json.dumps({'ALL_DONE':True,'need':len(need),'bad':bad}))
