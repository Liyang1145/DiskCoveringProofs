"""Audit registry dependency reachability/status; NOT validation of mathematics."""
import json
from pathlib import Path
P=Path(__file__).resolve().parent;rows=[json.loads(x)for x in Path('.mathlab/claims.jsonl').read_text(encoding='utf-8').splitlines()if x.strip()];claims={};events={}
for r in rows:
 if r.get('kind')=='claim':claims[r['id']]=r
 else:
  for k in ['target','claimId','id']:
   if k in r:events.setdefault(r[k],[]).append(r);break
seen=set();missing=[]
def visit(i):
 if i in seen:return
 seen.add(i)
 if i not in claims:missing.append(i);return
 for j in claims[i].get('dependsOn',[]):visit(j)
for i in ['C1370','C1330']:visit(i)
flags=[]
for i in sorted(seen,key=lambda x:int(x[1:])):
 if i not in claims:continue
 c=claims[i];e=events.get(i,[])
 if c['status']not in ['proved','proved-interval','proved-exact'] or any('retract'in str(r.get('kind','')).lower()for r in e):flags.append(dict(id=i,status=c['status'],events=e,statement=c['statement']))
out=dict(status='registry_only_not_truth',roots=['C1370','C1330'],ancestor_count=len(seen),ids=sorted(seen,key=lambda x:int(x[1:])),missing=missing,flags=flags,event_kinds=sorted({r.get('kind','')for r in rows}))
(P/'final-claim-dependency-check.json').write_text(json.dumps(out,indent=2));print('ancestors',len(seen),'missing',missing,'flags',[(x['id'],x['status'])for x in flags],'eventkinds',out['event_kinds'])
