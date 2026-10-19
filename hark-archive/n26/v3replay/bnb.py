import os as _os, sys as _sys  # hark-archive portable paths (see hark-archive/_paths.py)
_hd = _os.path.dirname(_os.path.abspath(__file__))
while _os.path.basename(_hd) != 'hark-archive' and _os.path.dirname(_hd) != _hd: _hd = _os.path.dirname(_hd)
_sys.path.append(_hd); from _paths import DCP_N26
import sys,json,os,time
from fractions import Fraction as F
import numpy as np, mpmath as mp
import propose as PP
from n26_force import angular_domain, tighten
mat=angular_domain(PP.spec)
B=json.load(open('boxes.json'))['boxes']
def save(path,obj):
    tmp=path+'.tmp'; json.dump(obj,open(tmp,'w')); os.replace(tmp,path)
def run(t,budget,path=None,box=None):
    path=path or f'subtrees/{t}.json'
    if os.path.exists(path): st=json.load(open(path))
    else:
        lo,hi=box if box else (B[t]['lo'],B[t]['hi'])
        st={'target':t,'nodes':[None],'stack':[[0,[str(x) for x in lo],[str(x) for x in hi]]],'minmargin':None,'done':False}
    t0=time.time()
    while st['stack'] and time.time()-t0<budget:
        idx,lo,hi=st['stack'].pop()
        lo=[F(x) for x in lo];hi=[F(x) for x in hi]
        bx=tighten(mat,lo,hi)
        if bx is None: st['nodes'][idx]={'kind':'EMPTY'}; continue
        lo,hi=bx
        try:
            v,Gv,Fv=PP.propose(lo,hi)
            c,m=PP.rationalize(lo,hi,Gv,Fv)
        except Exception as e:
            c,m=None,None; Gv=None
        if m is not None and m>0:
            st['nodes'][idx]={'kind':'FORCE','cert':c}
            st['minmargin']=str(m) if st['minmargin'] is None else str(min(F(st['minmargin']),m))
            continue
        # split axis: largest penalty
        w=[h-l for l,h in zip(lo,hi)]
        if Gv is not None:
            pen=[]
            for i in range(len(lo)):
                gi=np.linalg.norm(Gv[i]); H=float(w[i])*3.1416
                pen.append(H*gi+H*H*gi)
            ax=int(np.argmax(pen))
            if w[ax]==0: ax=max(range(len(w)),key=lambda i:w[i])
        else: ax=max(range(len(w)),key=lambda i:w[i])
        mid=(lo[ax]+hi[ax])/2
        assert lo[ax]<mid<hi[ax]
        c0=len(st['nodes']);st['nodes']+= [None,None]
        st['nodes'][idx]={'kind':'SPLIT','axis':ax,'mid':str(mid),'children':[c0,c0+1]}
        lu=list(hi);lu[ax]=mid;rl=list(lo);rl[ax]=mid
        st['stack'].append([c0+1,[str(x) for x in rl],[str(x) for x in hi]])
        st['stack'].append([c0,[str(x) for x in lo],[str(x) for x in lu]])
    st['done']=not st['stack']
    save(path,st)
    from collections import Counter
    return {'target':t,'done':st['done'],'counts':dict(Counter(n['kind'] for n in st['nodes'] if n)),'pending':len(st['stack']),'minmargin':st['minmargin'] and float(F(st['minmargin']))}
if __name__=='__main__':
    budget=float(sys.argv[1]); ts=sys.argv[2:]
    t0=time.time()
    for t in ts:
        left=budget-(time.time()-t0)
        if left<5: break
        r=run(t,left); r['t']=time.time()
        print(json.dumps(r),flush=True)
        with open(DCP_N26+'/ledger.jsonl','a') as f: f.write(json.dumps({'event':'v3-replay-bnb',**r})+'\n')
