"""Disjoint pending-root worker. Never writes main manifest. Merge must validate tree."""
import sys,json,hashlib,time
from pathlib import Path
from fractions import Fraction as F
import hubline_domain as D
P=D.H.K.P
BASE=P/'evidence/hubline-domain-stage11825.json'
raw=BASE.read_bytes();base=json.loads(raw)
roots=[]
for i,b in enumerate(base['pending']):
    boxes=[D.decode(b)]
    if i==0:
        for _ in range(2):
            new=[]
            for B in boxes:
                k=max(range(3),key=lambda j:B[j][1]-B[j][0]);lo,hi=B[k];mid=(lo+hi)/2
                for pair in [(lo,mid),(mid,hi)]:
                    C=list(B);C[k]=pair;new.append(tuple(C))
            boxes=new
    roots.extend((i,B) for B in boxes)
bid=int(sys.argv[1]);parent,root=roots[bid]
out=P/'evidence/parallel-domain';out.mkdir(exist_ok=True)
D.OUT=out/f'branch-{bid}.json'
if not D.OUT.exists():
    D.OUT.write_text(json.dumps({'pending':[D.encode(root)],'leaves':[],'counts':{'infeasible':0,'certified':0,'split':0,'processed':0}}))
original_save=D.save_state
def save(stack,leaves,counts):
    state=original_save(stack,leaves,counts)
    state.update(branch_id=bid,parent_pending_index=parent,branch_root=D.encode(root),base_sha256=hashlib.sha256(raw).hexdigest(),worker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    tmp=D.OUT.with_suffix('.tmp');tmp.write_text(json.dumps(state,indent=2));tmp.replace(D.OUT)
    return state
D.save_state=save
for _ in range(1000):
    before=json.loads(D.OUT.read_text());n=before['counts']['processed']
    if not before['pending']:break
    D.run(20)
    after=json.loads(D.OUT.read_text())
    if after['counts']['processed']==n:break
