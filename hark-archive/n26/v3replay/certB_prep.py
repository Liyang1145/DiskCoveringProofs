"""Memory relief for checker B (same checks, same code): loads tree + B's walk cache once, re-runs certB_v3.main's
base-tree consistency asserts, and writes per-shard pending work lists verB_pending_<shard>.pkl containing
(i,kind,lo,hi,target,node) for leaves not yet in verB_v3_<shard>.json. certB_lite.py then checks them with
certB_v3.force_B / local certB.check_leaf without loading the 258 MB tree. usage: certB_prep.py <nshards>"""
import os as _os, sys as _sys  # hark-archive portable paths (see hark-archive/_paths.py)
_hd = _os.path.dirname(_os.path.abspath(__file__))
while _os.path.basename(_hd) != 'hark-archive' and _os.path.dirname(_hd) != _hd: _hd = _os.path.dirname(_hd)
_sys.path.append(_hd); from _paths import DCP_N26
import sys,os,json,hashlib,pickle
sys.path.insert(0,DCP_N26+'/v3replay')
from certB_v3 import ROOT
W=ROOT+'/v3replay/'; ns=int(sys.argv[1])
RAW=open(W+'V3-REPLAY-TREE.json','rb').read(); TSHA=hashlib.sha256(RAW).hexdigest()
D=json.loads(RAW); del RAW; spec=D['spec']; nodes=D['nodes']
base=json.load(open(ROOT+'/repo/cover26/proof_bundle/work/n26-sharp-candidate-angles-proposal-v3.json'))
assert base['spec']==spec
T=set(int(x) for x in D['closed_targets'])
for i,n in enumerate(base['nodes']):
    if i in T: assert n=={'kind':'OPEN'}
    else: assert nodes[i]==n, i
del base
C=pickle.load(open(W+'verB_walkcache.pkl','rb')); assert C['sha']==TSHA
for sh in range(ns):
    st=W+f'verB_v3_{sh}.json'; S=json.load(open(st)) if os.path.exists(st) else {'done':{}}
    P=[(i,k,lo,hi,tg,nodes[i]) for (i,k,lo,hi,tg) in C['leaves'] if i%ns==sh and not (str(i) in S['done'] and S['done'][str(i)]['kind']==k)]
    tot=sum(1 for l in C['leaves'] if l[0]%ns==sh)
    pickle.dump({'sha':TSHA,'spec':spec,'pending':P,'leaves_in_shard':tot,'cnt':C['cnt']},open(W+f'verB_pending_{sh}.pkl.tmp','wb'))
    os.replace(W+f'verB_pending_{sh}.pkl.tmp',W+f'verB_pending_{sh}.pkl')
    print(sh,len(P),tot)
