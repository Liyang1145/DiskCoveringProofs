"""Checker A replay of V3-REPLAY-TREE.json: archive tighten/force_check for FORCE; LOCAL-SLAB leaf files
(produced by local/certA.leaf_bound) checked for sha, box containment, b-range coverage, positive bounds."""
import sys,json,os,hashlib,time
from fractions import Fraction as F
SRC='/workspace/work/dcp-n26/repo/cover26/proof_bundle/outputs/n26-sharp-candidate-angles-published-replay-v1'
sys.path.insert(0,SRC); sys.path.insert(0,'/workspace/work/dcp-n26/local'); sys.path.insert(0,'/workspace/work/dcp-n26')
from n26_force import angular_domain, rootbox, tighten, load_trig
from n26_direct_arc_force import force_check
import prop
RUP=F("0.234700090400448239616790133776692127560495963654971391785925")
D=json.load(open('V3-REPLAY-TREE.json')); spec=D['spec']; nodes=D['nodes']; arcs=load_trig()[0]
mat=angular_domain(spec); lo,hi=rootbox(mat)
stack=[(0,lo,hi)]; seen=set(); cnt={}; fmin=None; lmin=None; opens=[]
while stack:
    i,lo,hi=stack.pop(); assert i not in seen; seen.add(i); n=nodes[i]; k=n['kind']; cnt[k]=cnt.get(k,0)+1
    b=tighten(mat,lo,hi)
    if k=='EMPTY': assert b is None; continue
    assert b is not None; lo,hi=b
    if k=='SPLIT':
        a=n['axis'];m=F(n['mid']); assert lo[a]<m<hi[a] and all(c>i for c in n['children'])
        lu=list(hi);lu[a]=m;rl=list(lo);rl[a]=m
        stack.append((n['children'][1],rl,list(hi))); stack.append((n['children'][0],list(lo),lu)); continue
    if k=='FORCE':
        r=force_check(spec,lo,hi,n['cert'],arcs); m=F(r['required_radius_lower'])-RUP; assert m>0,i
        fmin=m if fmin is None else min(fmin,m)
    elif k=='LOCAL-SLAB':
        p='/workspace/work/dcp-n26/'+n['file']; assert hashlib.sha256(open(p,'rb').read()).hexdigest()==n['sha256']
        d=json.load(open(p)); L=[F(x) for x in d['lower']]; H=[F(x) for x in d['upper']]
        assert all(a<=x and y<=c for a,x,y,c in zip(L,lo,hi,H)), i
        b1,b2=prop.brange(lo,hi); ps=d['pieces']
        assert d['closed'] and F(ps[0]['ba'])<=b1 and F(ps[-1]['bb'])>=b2
        for x,y in zip(ps,ps[1:]): assert x['bb']==y['ba']
        for x in ps: assert 'OPEN' not in x and F(x['bound'])>0
        mb=min(F(x['bound']) for x in ps); lmin=mb if lmin is None else min(lmin,mb)
    elif k=='OPEN': opens.append(i)
    elif k=='LOCAL': pass
    else: raise ValueError(k)
assert len(seen)==len(nodes) and cnt['SPLIT']+1==sum(v for kk,v in cnt.items() if kk!='SPLIT')
res={'checker':'A','nodes':len(nodes),'counts':cnt,'open':opens,'min_force_margin_over_RUP':str(fmin),'min_force_margin_float':float(fmin),
     'min_local_slab_energy_bound':float(lmin),'tree_sha256':hashlib.sha256(open('V3-REPLAY-TREE.json','rb').read()).hexdigest()}
json.dump(res,open('verA.json.tmp','w'),indent=1); os.replace('verA.json.tmp','verA.json'); print(json.dumps(res))
