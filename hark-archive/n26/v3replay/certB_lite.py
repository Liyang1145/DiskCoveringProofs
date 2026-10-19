"""Low-memory checker-B worker: identical per-leaf checks to certB_v3.main (FORCE via certB_v3.force_B, LOCAL-SLAB via
local certB.check_leaf / verB_shared.json), reading the work list from verB_pending_<shard>.pkl (made by certB_prep.py
from B's own walk). Verifies the tree file sha matches the pending list. usage: certB_lite.py <budget> <shard> <nshards>"""
import os as _os, sys as _sys  # hark-archive portable paths (see hark-archive/_paths.py)
_hd = _os.path.dirname(_os.path.abspath(__file__))
while _os.path.basename(_hd) != 'hark-archive' and _os.path.dirname(_hd) != _hd: _hd = _os.path.dirname(_hd)
_sys.path.append(_hd); from _paths import DCP_N26
import sys,os,json,time,hashlib,pickle
from fractions import Fraction as F
sys.path.insert(0,DCP_N26+'/v3replay')
from certB_v3 import ROOT,RUP,force_B,LB
BUD=float(sys.argv[1]); shard=int(sys.argv[2]); ns=int(sys.argv[3]); T0=time.time()
W=ROOT+'/v3replay/'
h=hashlib.sha256()
with open(W+'V3-REPLAY-TREE.json','rb') as fh:
    for blk in iter(lambda: fh.read(1<<24), b''): h.update(blk)
TSHA=h.hexdigest()
PK=pickle.load(open(W+f'verB_pending_{shard}'+os.environ.get('BSUF','')+'.pkl','rb')); assert PK['sha']==TSHA
spec=PK['spec']
st=W+f'verB_v3_{shard}'+os.environ.get('BSUF','')+'.json'; S=json.load(open(st)) if os.path.exists(st) else {'done':{}}
def save():
    tp=st+f'.tmp{os.getpid()}'; json.dump(S,open(tp,'w')); os.replace(tp,st)
SHB={}; cache={}; PJ=json.load(open(ROOT+'/local/prop.json')); V=[F(x) for x in PJ['v']]
n0=0
for (i,k,lo,hi,tg,node) in PK['pending']:
    if i%ns!=shard or (str(i) in S['done'] and S['done'][str(i)]['kind']==k): continue
    if time.time()-T0>BUD: break
    if k=='FORCE':
        L=force_B(spec,lo,hi,node['cert'],cache); assert L is not None and L>RUP,(i,L)
        S['done'][str(i)]={'kind':k,'target':tg,'margin':str(L-RUP)}
    elif k=='LOCAL-SLAB':
        p=ROOT+'/'+node['file']; raw=open(p,'rb').read(); assert hashlib.sha256(raw).hexdigest()==node['sha256']
        d=json.loads(raw); mu=F(d['mu']); assert mu>=0
        b1=sum(min(v*(a-c),v*(bb-c)) for v,a,bb,c in zip(V,lo,hi,LB.CS)); b2=sum(max(v*(a-c),v*(bb-c)) for v,a,bb,c in zip(V,lo,hi,LB.CS))
        if node['file'].startswith('v3replay/lleaves/shared/'):
            SH=SHB.setdefault('x',json.load(open(W+'verB_shared.json')))
            e=SH[os.path.basename(p)]; assert e['ok'] and e['sha256']==node['sha256']
            FL=[F(x) for x in e['lower']]; FH=[F(x) for x in e['upper']]
            assert all(a<=x and y<=c for a,x,y,c in zip(FL,lo,hi,FH)),(i,'node box not inside shared file box')
            assert F(e['b_cov'][0])<=b1 and F(e['b_cov'][1])>=b2
            S['done'][str(i)]={'kind':k,'target':tg,'min_energy_bound':e['min_bound'],'via':'shared'}
        else:
            ps=d['pieces']; assert F(ps[0]['ba'])<=b1 and F(ps[-1]['bb'])>=b2
            for x,y in zip(ps,ps[1:]): assert x['bb']==y['ba']
            worst=None; PP=S.setdefault('partial',{}).setdefault(str(i),{'sha':node['sha256'],'p':{}})
            assert PP['sha']==node['sha256']; stopped=False
            for j,x in enumerate(ps):
                ba,bb_=F(x['ba']),F(x['bb'])
                if bb_<b1 or ba>b2: continue
                if str(j) in PP['p']: bd=F(PP['p'][str(j)])
                else:
                    if time.time()-T0>BUD: stopped=True; break
                    kap=F(x['kappa']); w=[a+kap*t for a,t in zip(LB.L0,LB.TAU)]; assert all(y>=0 for y in w)
                    bd=LB.check_leaf(w,lo,hi,ba,bb_,mu); assert bd is not None and bd>0,(i,x['ba'])
                    PP['p'][str(j)]=str(bd)
                worst=bd if worst is None else min(worst,bd)
            if stopped: break
            S['done'][str(i)]={'kind':k,'target':tg,'min_energy_bound':str(worst)}; del S['partial'][str(i)]
    elif k=='OPEN': S['done'][str(i)]={'kind':k,'target':tg}
    elif k=='LOCAL': S['done'][str(i)]={'kind':k,'target':tg,'note':'archive LOCAL leaf (pinning cell), not re-checked here'}
    else: raise ValueError(k)
    n0+=1
    if n0%300==0: save()
save()
left=sum(1 for (i,k,*_) in PK['pending'] if not (str(i) in S['done'] and S['done'][str(i)]['kind']==k))
tot=PK['leaves_in_shard']
print(json.dumps({'shard':shard,'leaves_in_shard':tot,'done':tot-left,'complete':left==0,'counts':PK['cnt']}))
