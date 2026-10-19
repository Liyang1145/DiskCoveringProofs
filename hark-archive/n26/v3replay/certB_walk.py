"""Resumable version of checker B's tree walk (same code path: certB_v3.domain / certB_v3.tight, B's own
re-implementation). Produces verB_walkcache.pkl {'sha','leaves','cnt'} exactly as certB_v3.main would, but in
<=budget chunks (state in verB_walk_state.pkl + verB_walk_part_*.pkl). usage: certB_walk.py <budget_s>"""
import sys,os,json,time,hashlib,pickle,glob
from fractions import Fraction as F
sys.path.insert(0,'/workspace/work/dcp-n26/v3replay')
from certB_v3 import domain,tight,SC,ROOT
T0=time.time(); BUD=float(sys.argv[1])
W=ROOT+'/v3replay/'; STF=W+'verB_walk_state.pkl'; CP=W+'verB_walkcache.pkl'
RAW=open(W+'V3-REPLAY-TREE.json','rb').read(); TSHA=hashlib.sha256(RAW).hexdigest()
if os.path.exists(CP) and pickle.load(open(CP,'rb'))['sha']==TSHA: print(json.dumps({'walk':'already cached'})); sys.exit(0)
D=json.loads(RAW); spec=D['spec']; nodes=D['nodes']; T=set(int(x) for x in D['closed_targets'])
M=domain(spec)
S=pickle.load(open(STF,'rb')) if os.path.exists(STF) else None
if S is None or S['sha']!=TSHA:
    for p in glob.glob(W+'verB_walk_part_*.pkl'): os.remove(p)
    b=spec['B']; lo=[F(-M[i][0],SC) for i in range(1,b)]; hi=[F(M[0][i],SC) for i in range(1,b)]
    S={'sha':TSHA,'stack':[(0,lo,hi,None)],'seen':bytearray(len(nodes)),'cnt':{},'part':0}
stack=S['stack']; seen=S['seen']; cnt=S['cnt']; leaves=[]
while stack and time.time()-T0<BUD:
    i,lo,hi,tg=stack.pop(); assert not seen[i]; seen[i]=1
    n=nodes[i]; k=n['kind']; cnt[k]=cnt.get(k,0)+1
    if i in T: tg=i
    bx=tight(M,lo,hi)
    if k=='EMPTY': assert bx is None; continue
    assert bx is not None; lo,hi=bx
    if k=='SPLIT':
        a=n['axis']; m=F(n['mid']); assert lo[a]<m<hi[a]
        assert len(n['children'])==2 and all(c>i for c in n['children'])
        h1=list(hi); h1[a]=m; l2=list(lo); l2[a]=m
        stack.append((n['children'][1],l2,list(hi),tg)); stack.append((n['children'][0],list(lo),h1,tg)); continue
    leaves.append((i,k,lo,hi,tg))
pf=W+f'verB_walk_part_{S["part"]:04d}.pkl'
pickle.dump(leaves,open(pf+'.tmp','wb')); os.replace(pf+'.tmp',pf); S['part']+=1
pickle.dump(S,open(STF+'.tmp','wb')); os.replace(STF+'.tmp',STF)
if stack:
    print(json.dumps({'walk':'partial','seen':sum(seen),'of':len(nodes),'stack':len(stack)})); sys.exit(0)
assert sum(seen)==len(nodes) and cnt['SPLIT']+1==len(nodes)-cnt['SPLIT']
allL=[]
for p in sorted(glob.glob(W+'verB_walk_part_*.pkl')): allL+=pickle.load(open(p,'rb'))
pickle.dump({'sha':TSHA,'leaves':allL,'cnt':cnt},open(CP+'.tmp','wb')); os.replace(CP+'.tmp',CP)
print(json.dumps({'walk':'complete','leaves':len(allL),'cnt':cnt}))
