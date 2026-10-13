"""Generic immutable-plan worker; outputs branch-local frontier, never a global claim.
CLI PLAN BRANCH_ID OUTPUT_DIR. Canonical plan validated before any work.
"""
import sys,json,hashlib
from pathlib import Path
import hubline_domain as D
P=D.H.K.P
sys.path.insert(0,str(P/'members/structure/parallel-domain'))
import plan_branches as PB
planpath=Path(sys.argv[1]);raw=planpath.read_bytes();plan=json.loads(raw);psha=hashlib.sha256(raw).hexdigest()
source=Path(plan['source']['path'])
if not source.exists():source=planpath.parent/source
problems,snap=PB.check_plan(plan,source);assert not problems,problems
bid=int(sys.argv[2]);ent=next(b for b in plan['branches'] if b['id']=='b%02d'%bid)
root=D.decode(ent['root']);outdir=Path(sys.argv[3]);outdir.mkdir(exist_ok=True,parents=True)
D.OUT=outdir/f'branch-{bid}.json'
meta=dict(branch_id=bid,parent_pending_index=ent['parent_index'],branch_root=D.encode(root),base_sha256=snap['sha256'],plan_sha256=psha,worker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
def save(stack,leaves,counts):
 state=dict(status='branch complete' if not stack else 'partial',domain=plan['domain'],counts=counts,pending=[D.encode(b) for b in stack],leaves=leaves,**meta)
 state['hashes']={Path(m.__file__).name:hashlib.sha256(Path(m.__file__).read_bytes()).hexdigest() for m in [D,D.AF,D.AF.A,D.H]}
 tmp=D.OUT.with_suffix('.tmp');tmp.write_text(json.dumps(state,indent=2));tmp.replace(D.OUT);return state
D.save_state=save
if D.OUT.exists():
 d=json.loads(D.OUT.read_bytes())
 assert all(d.get(k)==v for k,v in meta.items()),'resume provenance mismatch'
else:save([root],[],dict(infeasible=0,certified=0,split=0,processed=0))
for _ in range(1000):
 before=json.loads(D.OUT.read_bytes());n=before['counts']['processed']
 if not before['pending']:break
 D.run(10)
 after=json.loads(D.OUT.read_bytes())
 if after['counts']['processed']==n:break
