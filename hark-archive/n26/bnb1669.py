"""Box 1669 (contains the exact D2 candidate on its boundary).
Top-level tree: exact complement decomposition of 1669 around the archive's
refined-anchor-pinning closed anchor-angle cell C (cover26/proof_bundle/work/
n26-refined-anchor-pinning-broad-proposal-v2.json, sha256 82a87672...b2e):
for each axis k, SPLIT at C_lo[k] / C_hi[k] when strictly interior; the final
middle box is a subset of C -> leaf kind LOCAL-PINNING-CELL (paid by the archive's
refined pinning + centered local barrier, NOT re-proved here).  Every slab is a
separate job certified by the same robust-weight energy B&B as bnb2.py and
checkpointed in certs1669/slab_<n>.json; assemble() writes certs/1669.json."""
import os as _os, sys as _sys  # hark-archive portable paths (see hark-archive/_paths.py)
_hd = _os.path.dirname(_os.path.abspath(__file__))
while _os.path.basename(_hd) != 'hark-archive' and _os.path.dirname(_hd) != _hd: _hd = _os.path.dirname(_hd)
_sys.path.append(_hd); from _paths import DCP_N26
import json, os, sys, time, hashlib
from fractions import Fraction as F
import numpy as np
import certify_box as cb, robust as rb, robust2 as rb2
ROOT=DCP_N26; DEN=10**15; FLOOR=float(os.environ.get('FLOOR','1e-11'))
PROP=ROOT+'/repo/cover26/proof_bundle/work/n26-refined-anchor-pinning-broad-proposal-v2.json'
CELL=[(F(a),F(b)) for a,b in json.load(open(PROP))['closed_anchor_angle_cells']]
B=[b for b in json.load(open(ROOT+'/pending.json'))['pending_closed_leaf_boxes'] if b['index']==1669][0]
LO=[F(x) for x in B['lower']]; HI=[F(x) for x in B['upper']]
TH=np.array({r['index']:r for r in json.load(open(ROOT+'/diag_merged.json'))}[1669]['None'][1])
PST=None
OUT=ROOT+'/certs1669'; os.makedirs(OUT,exist_ok=True)
def skeleton():
    """returns tree with SLAB placeholders and list of slab boxes."""
    slabs=[]
    def build(lo,hi,k):
        while k<15 and not (lo[k]<CELL[k][0]<hi[k] or lo[k]<CELL[k][1]<hi[k]):
            assert CELL[k][0]<=lo[k] and hi[k]<=CELL[k][1], ('axis not inside cell',k)
            k+=1
        if k==15:
            return {'kind':'LOCAL-PINNING-CELL'}
        c0,c1=CELL[k]
        if lo[k]<c0<hi[k]:
            h1=list(hi);h1[k]=c0; l2=list(lo);l2[k]=c0; slabs.append((lo,h1))
            return {'kind':'SPLIT','axis':k,'mid':str(c0),'children':[{'kind':'SLAB','n':len(slabs)-1},build(l2,hi,k)]}
        h1=list(hi);h1[k]=c1; l2=list(lo);l2[k]=c1; slabs.append((l2,hi))
        return {'kind':'SPLIT','axis':k,'mid':str(c1),'children':[build(lo,h1,k+1),{'kind':'SLAB','n':len(slabs)-1}]}
    return build(LO,HI,0),slabs
def wint(w): return [int(x*DEN) for x in cb.rationalize_weights(w,floor=FLOOR,den=DEN)]
def certify_slab(n):
    import shells1669
    tree0,slabs=shells1669.skeleton(); lo0,hi0,_j=slabs[n]
    path=OUT+'/slab_%d.json'%n
    if os.path.exists(path):
        c=json.load(open(path))
        if c['open']==0: return {'slab':n,'skip':True}
    cache={}
    def kern(wn):
        k=tuple(wn)
        if k not in cache:
            if len(cache)>64: cache.clear()
            cache[k]=cb.exact_pairs([F(x,DEN) for x in wn])
        return cache[k]
    def rig(wn,lo,hi):
        p,W=kern(wn); bd,_=cb.box_bound(p,W,lo,hi); return (bd/W) if bd is not None else None
    global PST
    if PST is None: PST=rb2.ref_positions(TH)
    lam,_=cb.fit_weights(TH); t0=time.time(); nodes=0; rng=np.random.default_rng(n); TB=float(os.environ.get('TBOX','10800'))
    stats={'minw':1e9}
    def rec(lo,hi,wprev,depth):
        nonlocal nodes; nodes+=1
        if time.time()-t0>TB: return {'kind':'OPEN','reason':'budget'}
        if wprev is not None:
            m=rig(wint(wprev),lo,hi)
            if m is not None and m>0: return {'kind':'LEAF','w':wint(wprev),'margin_over_W':str(m)}
        lof=np.array([float(x) for x in lo]); hif=np.array([float(x) for x in hi])
        hit={}
        def cbk(wc):
            m=rig(wint(wc),lo,hi)
            if m is not None and m>0: hit['m']=m; hit['w']=wint(wc); return True
            return False
        w,v,ok=rb2.robust3(lof,hif,wprev if wprev is not None else lam,PST,iters=int(os.environ.get('ITERS','30')),callback=cbk,floor=FLOOR,rng=rng)
        if ok and 'w' in hit: return {'kind':'LEAF','w':hit['w'],'margin_over_W':str(hit['m'])}
        if depth>=80: return {'kind':'OPEN','reason':'depth'}
        r=[h-l for l,h in zip(lo,hi)]; ax=max(range(15),key=lambda k:r[k]); mid=(lo[ax]+hi[ax])/2
        h1=list(hi);h1[ax]=mid; l2=list(lo);l2[ax]=mid
        return {'kind':'SPLIT','axis':ax,'mid':str(mid),'children':[rec(lo,h1,w,depth+1),rec(l2,hi,w,depth+1)]}
    tree=rec(lo0,hi0,None,0)
    def cnt(t,k): return sum(cnt(c,k) for c in t['children']) if t['kind']=='SPLIT' else int(t['kind']==k)
    out={'slab':n,'lower':[str(x) for x in lo0],'upper':[str(x) for x in hi0],'tree':tree,'leaves':cnt(tree,'LEAF'),'open':cnt(tree,'OPEN'),'nodes':nodes,'seconds':time.time()-t0}
    tmp=path+'.%d.tmp'%os.getpid(); json.dump(out,open(tmp,'w')); os.replace(tmp,path)
    with open(OUT+'/ledger.jsonl','a') as f: f.write(json.dumps({k:out[k] for k in ['slab','leaves','open','nodes','seconds']})+'\n')
    return {k:out[k] for k in ['slab','leaves','open','nodes','seconds']}
def assemble(stop=0):
    import shells1669
    tree,slabs=shells1669.skeleton(stop)
    def fill(t):
        if t['kind']=='SLAB':
            c=json.load(open(OUT+'/slab_%d.json'%t['n']))
            lo,hi,_=slabs[t['n']]
            assert c['lower']==[str(x) for x in lo] and c['upper']==[str(x) for x in hi], 'slab box mismatch %d'%t['n']
            return c['tree']
        if t['kind']=='SPLIT': t['children']=[fill(c) for c in t['children']]
        return t
    tree=fill(tree)
    def cnt(t,k): return sum(cnt(c,k) for c in t['children']) if t['kind']=='SPLIT' else int(t['kind']==k)
    out={'index':1669,'lower':B['lower'],'upper':B['upper'],'weight_den':DEN,'method':'bnb2-robust+LOCAL-PINNING-CELL',
         'local_cell_source':{'file':'cover26/proof_bundle/work/n26-refined-anchor-pinning-broad-proposal-v2.json','sha256':hashlib.sha256(open(PROP,'rb').read()).hexdigest(),'cells':[[str(a),str(b)] for a,b in CELL]},
         'tree':tree,'leaves':cnt(tree,'LEAF'),'local_leaves':cnt(tree,'LOCAL-PINNING-CELL'),'open':cnt(tree,'OPEN')}
    tmp=ROOT+'/certs/.1669.tmp'; json.dump(out,open(tmp,'w')); os.replace(tmp,ROOT+'/certs/1669.json'); return {k:out[k] for k in ['leaves','local_leaves','open']}
if __name__=='__main__':
    if sys.argv[1]=='skel':
        t,s=skeleton(); print(len(s)); 
        for i,(lo,hi) in enumerate(s): print(i,[ '%.2e'%float(h-l) for l,h in zip(lo,hi)][6:])
    elif sys.argv[1]=='assemble': print(assemble(int(sys.argv[2]) if len(sys.argv)>2 else 0))
    else:
        from multiprocessing import Pool
        ids=[int(x) for x in sys.argv[1].split(',')]
        with Pool(int(os.environ.get('NP','2'))) as p:
            for r in p.imap_unordered(certify_slab,ids,chunksize=1): print(json.dumps(r),flush=True)
