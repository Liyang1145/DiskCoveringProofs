"""Checker A, per-target, resumable: walks V3-REPLAY-TREE.json from root with archive tighten; for leaves under the
given targets: FORCE -> archive force_check vs RUP; LOCAL-SLAB -> sha + containment + b-range coverage + positive bounds
(bounds produced by local/certA.leaf_bound). State: verA_open23.json. usage: replayA_t.py <budget> <targets...>"""
import sys,json,os,hashlib,time
from fractions import Fraction as F
SRC='/workspace/work/dcp-n26/repo/cover26/proof_bundle/outputs/n26-sharp-candidate-angles-published-replay-v1'
sys.path.insert(0,SRC); sys.path.insert(0,'/workspace/work/dcp-n26/local'); sys.path.insert(0,'/workspace/work/dcp-n26')
from n26_force import angular_domain, rootbox, tighten, load_trig
from n26_direct_arc_force import force_check
import prop
RUP=F("0.234700090400448239616790133776692127560495963654971391785925")
T0=time.time(); BUD=float(sys.argv[1]); TG=set(int(x) for x in sys.argv[2:])
ALLT={1,5,9,13,17,21,25,29,33,37,41,45,48,44,40,36,32,24,20,16,12,8,4}
raw=open('V3-REPLAY-TREE.json','rb').read(); SHA=hashlib.sha256(raw).hexdigest()
D=json.loads(raw); spec=D['spec']; nodes=D['nodes']; arcs=load_trig()[0]
ST='verA_open23.json'; S=json.load(open(ST)) if os.path.exists(ST) else {}
def save():
    json.dump(S,open(ST+'.tmp','w')); os.replace(ST+'.tmp',ST)
mat=angular_domain(spec)
import pickle
par={}
for i,n in enumerate(nodes):
    if n['kind']=='SPLIT':
        for c in n['children']: assert c not in par; par[c]=i
ANC=set()
for t in ALLT:
    x=t
    while x in par: x=par[x]; ANC.add(x)
def walk(i0,lo,hi,descend):
    """archive-tighten walk from node i0 with box (lo,hi); descend(i) says whether to enter children."""
    out=[]; stack=[(i0,lo,hi)]
    while stack:
        i,lo,hi=stack.pop(); n=nodes[i]; k=n['kind']
        b=tighten(mat,lo,hi)
        if k=='EMPTY': assert b is None; continue
        assert b is not None; lo,hi=b
        if k=='SPLIT':
            a=n['axis'];m=F(n['mid']); assert lo[a]<m<hi[a] and all(c>i for c in n['children'])
            lu=list(hi);lu[a]=m;rl=list(lo);rl[a]=m
            for c,(l_,h_) in ((n['children'][1],(rl,list(hi))),(n['children'][0],(list(lo),lu))):
                if descend(c): stack.append((c,l_,h_))
                else: out.append(('ROOT',c,l_,h_))
            continue
        out.append((i,k,lo,hi))
    return out
CP='verA_roots.pkl'; RC=pickle.load(open(CP,'rb')) if os.path.exists(CP) else None
if RC is None or RC['sha']!=SHA:
    lo,hi=rootbox(mat)
    r=walk(0,lo,hi,lambda c: c in ANC)
    roots={c:(l,h) for tag,c,l,h in [x for x in r if x[0]=='ROOT'] if c in ALLT}
    assert set(roots)==ALLT
    RC={'sha':SHA,'roots':roots}; pickle.dump(RC,open(CP+'.tmp','wb')); os.replace(CP+'.tmp',CP)
leaves=[]
for t in sorted(TG):
    wp=f'verA_walk_{t}.pkl'; W=pickle.load(open(wp,'rb')) if os.path.exists(wp) else None
    if W is None or W['sha']!=SHA:
        if time.time()-T0>BUD-30: print(json.dumps({'stop':'walk','t':t})); sys.exit(0)
        l,h=RC['roots'][t]; W={'sha':SHA,'leaves':walk(t,l,h,lambda c: True)}
        pickle.dump(W,open(wp+'.tmp','wb')); os.replace(wp+'.tmp',wp)
    leaves+=[(i,k,lo,hi,t) for (i,k,lo,hi) in W['leaves']]
for t in TG:
    rec=S.get(str(t))
    if rec is None or rec.get('tree_sha')!=SHA: rec=S[str(t)]={'tree_sha':SHA,'checked':{},'complete':False}
for (i,k,lo,hi,tg) in leaves:
    rec=S[str(tg)]
    if str(i) in rec['checked']: continue
    if time.time()-T0>BUD: save(); print(json.dumps({'stop':True,'done':{t:len(S[str(t)]['checked']) for t in TG}})); sys.exit(0)
    n=nodes[i]
    if k=='FORCE':
        r=force_check(spec,lo,hi,n['cert'],arcs); m=F(r['required_radius_lower'])-RUP; assert m>0,i
        rec['checked'][str(i)]=['F',str(m)]
    elif k=='LOCAL-SLAB':
        p='/workspace/work/dcp-n26/'+n['file']; assert hashlib.sha256(open(p,'rb').read()).hexdigest()==n['sha256']
        d=json.load(open(p)); L=[F(x) for x in d['lower']]; H=[F(x) for x in d['upper']]
        assert all(a<=x and y<=c for a,x,y,c in zip(L,lo,hi,H)), i
        b1,b2=prop.brange(lo,hi); ps=d['pieces']
        assert d['closed'] and F(ps[0]['ba'])<=b1 and F(ps[-1]['bb'])>=b2
        for x,y in zip(ps,ps[1:]): assert x['bb']==y['ba']
        for x in ps: assert 'OPEN' not in x and F(x['bound'])>0
        rec['checked'][str(i)]=['L',str(min(F(x['bound']) for x in ps))]
    else: raise ValueError((i,k))
    if len(rec['checked'])%200==0: save()
for t in TG:
    rec=S[str(t)]; mine=[l for l in leaves if l[4]==t]
    rec['complete']=len(rec['checked'])==len(mine)
    fm=[F(v) for kk,v in rec['checked'].values() if kk=='F']; lm=[F(v) for kk,v in rec['checked'].values() if kk=='L']
    rec['summary']={'force_leaves':len(fm),'local_slabs':len(lm),'force_min':float(min(fm)) if fm else None,'energy_min':float(min(lm)) if lm else None}
save(); print(json.dumps({t:S[str(t)]['summary']|{'complete':S[str(t)]['complete']} for t in TG}))
