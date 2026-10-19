"""After A (verA_open23.json complete) and B (verB_v3_*.json all leaves of target) pass: record closure in
V3-REPLAY-RESULT.json + ledger. usage: close_target.py <t>..."""
import os as _os, sys as _sys  # hark-archive portable paths (see hark-archive/_paths.py)
_hd = _os.path.dirname(_os.path.abspath(__file__))
while _os.path.basename(_hd) != 'hark-archive' and _os.path.dirname(_hd) != _hd: _hd = _os.path.dirname(_hd)
_sys.path.append(_hd); from _paths import DCP_N26
import sys,json,os,pickle,hashlib,time
from fractions import Fraction as F
R='V3-REPLAY-RESULT.json'; res=json.load(open(R))
sha=hashlib.sha256(open('V3-REPLAY-TREE.json','rb').read()).hexdigest()
C=pickle.load(open('verB_walkcache.pkl','rb')); assert C['sha']==sha,'B walk cache stale'
SB={}
for s in (0,1): SB.update({k:v for k,v in json.load(open(f'verB_v3_{s}.json'))['done'].items()})
A=json.load(open('verA_open23.json'))
for t in sys.argv[1:]:
    a=A[t]; assert a['tree_sha']==sha and a['complete'],('A not complete on current tree',t)
    mine=[l for l in C['leaves'] if l[4]==int(t)]
    fm=[];em=[]
    for (i,k,lo,hi,tg) in mine:
        d=SB.get(str(i)); assert d and d['kind']==k and k in ('FORCE','LOCAL-SLAB'),(t,i,k,d)
        if k=='FORCE': fm.append(F(d['margin']))
        else: em.append(F(d['min_energy_bound']))
    assert len(mine)==len(a['checked'])
    b={'force_leaves':len(fm),'local_slab_leaves':len(em),'min_force_margin':float(min(fm)),'min_energy_bound':float(min(em)) if em else None,'open_or_local':0}
    res['per_target'][t]={'A':a['summary'],'B':b,'tree_sha256':sha}
    lst=res.setdefault('closed_open23',[])
    if t not in lst: lst.append(t)
    res['remaining_open_v3_nodes']=[x for x in res['remaining_open_v3_nodes'] if str(x)!=t]
    with open(DCP_N26+'/ledger.jsonl','a') as f:
        f.write(json.dumps({'event':'v3-open23-CLOSED-A+B','target':t,'A':a['summary'],'B':b,'tree_sha256':sha,'t':time.time(),'cst':time.strftime('%Y-%m-%d %H:%M',time.gmtime(time.time()+8*3600))})+'\n')
    print(t,json.dumps(res['per_target'][t]))
res['tree_sha256']=sha
json.dump(res,open(R+'.tmp','w'),indent=1); os.replace(R+'.tmp',R)
