"""Resumable B&B v2: per-(sub)box ROBUST fitted weights (level-bundle max-min proposer,
robust.py, floats only propose) + the same rigorous verdict (certify_box.box_bound:
exact fmpq Schur, arb Taylor + cubic remainder, exact LDL PSD split, convex-QP plane).
Certificate format identical to bnb.py (checked by verify_certs.py, unchanged).
Each finished box: atomic write certs/<idx>.json, independent check by subprocess
verify_certs.py, append to ledger.jsonl."""
import json, os, sys, time, subprocess
from fractions import Fraction as F
import numpy as np
import certify_box as cb, robust as rb
ROOT='/workspace/work/dcp-n26'; DEN=10**12
BOX={b['index']:b for b in json.load(open(ROOT+'/pending.json'))['pending_closed_leaf_boxes']}
DIAG={r['index']:r for r in json.load(open(ROOT+'/diag_merged.json'))}
TBOX=float(os.environ.get('TBOX','2400'))
def verified_closed():
    s=set()
    if os.path.exists(ROOT+'/ledger.jsonl'):
        for l in open(ROOT+'/ledger.jsonl'):
            try: r=json.loads(l)
            except: continue
            if r.get('verify',{}).get('CLOSED') and os.path.exists(ROOT+'/certs/%d.json'%r['index']): s.add(r['index'])
    return s
def wint(w): return [int(x*DEN) for x in cb.rationalize_weights(w,den=DEN)]
def certify(idx):
    b=BOX[idx]; lo0=[F(x) for x in b['lower']]; hi0=[F(x) for x in b['upper']]
    cache={}
    def kern(wn):
        k=tuple(wn)
        if k not in cache:
            if len(cache)>64: cache.clear()
            cache[k]=cb.exact_pairs([F(x,DEN) for x in wn])
        return cache[k]
    def rig(wn,lo,hi):
        p,W=kern(wn); bd,_=cb.box_bound(p,W,lo,hi)
        return (bd/W) if bd is not None else None
    lam,_=cb.fit_weights(np.array(DIAG[idx]['None'][1]))
    t0=time.time(); nodes=0; rng=np.random.default_rng(idx)
    def rec(lo,hi,wprev,depth):
        nonlocal nodes; nodes+=1
        if time.time()-t0>TBOX: return {'kind':'OPEN','reason':'budget'}
        if wprev is not None:
            m=rig(wint(wprev),lo,hi)
            if m is not None and m>0: return {'kind':'LEAF','w':wint(wprev),'margin_over_W':str(m)}
        lof=np.array([float(x) for x in lo]); hif=np.array([float(x) for x in hi])
        w=wprev if wprev is not None else lam
        hit={}
        def cbk(wc):
            m=rig(wint(wc),lo,hi)
            if m is not None and m>0: hit['m']=m; hit['w']=wint(wc); return True
            return False
        w,v,ok=rb.robust_weights(lof,hif,w,iters=int(os.environ.get('ITERS','300')),rng=rng,callback=cbk,every=25,giveup=(80,-2e-4))
        if ok and 'w' in hit: return {'kind':'LEAF','w':hit['w'],'margin_over_W':str(hit['m']),'robust_float':v}
        if depth>=40: return {'kind':'OPEN','reason':'depth'}
        r=[h-l for l,h in zip(lo,hi)]; ax=max(range(15),key=lambda k:r[k]); mid=(lo[ax]+hi[ax])/2
        h1=list(hi);h1[ax]=mid; l2=list(lo); l2[ax]=mid
        return {'kind':'SPLIT','axis':ax,'mid':str(mid),'children':[rec(lo,h1,w,depth+1),rec(l2,hi,w,depth+1)]}
    tree=rec(lo0,hi0,None,0)
    def cnt(t,k): return sum(cnt(c,k) for c in t['children']) if t['kind']=='SPLIT' else int(t['kind']==k)
    out={'index':idx,'lower':b['lower'],'upper':b['upper'],'weight_den':DEN,'method':'bnb2-robust',
         'tree':tree,'leaves':cnt(tree,'LEAF'),'open':cnt(tree,'OPEN'),'nodes':nodes,'seconds':time.time()-t0}
    path=ROOT+'/certs/%d.json'%idx
    if os.path.exists(path):   # keep previous attempt
        os.replace(path, ROOT+'/certs_old/%d.%d.json'%(idx,int(time.time())))
    tmp=ROOT+'/certs/.%d.%d.tmp'%(idx,os.getpid()); json.dump(out,open(tmp,'w')); os.replace(tmp,path)
    ver={}
    try:
        res=subprocess.run(['python3',ROOT+'/verify_certs.py',path],capture_output=True,text=True,timeout=7200)
        ver=json.loads(res.stdout.strip().splitlines()[-1])
    except Exception as e: ver={'error':repr(e)[:200]}
    rec_={'index':idx,'leaves':out['leaves'],'open':out['open'],'nodes':nodes,'seconds':round(out['seconds'],1),'verify':ver,'t':time.time()}
    with open(ROOT+'/ledger.jsonl','a') as f: f.write(json.dumps(rec_)+'\n')
    return rec_
if __name__=='__main__':
    from multiprocessing import Pool
    os.makedirs(ROOT+'/certs_old',exist_ok=True)
    todo=[int(x) for x in sys.argv[1].split(',')] if len(sys.argv)>1 else json.load(open(ROOT+'/todo.json'))
    done=verified_closed(); todo=[i for i in todo if i not in done]
    print('todo',len(todo),flush=True)
    with Pool(int(os.environ.get('NP','2'))) as p:
        for r in p.imap_unordered(certify,todo,chunksize=1): print(json.dumps(r),flush=True)
