"""Find explicit file-name->SHA256 interfaces reachable from final graph/cut objects.
Integrity only. Missing unnamed hash lookup recorded separately, not guessed.
"""
from pathlib import Path
import json,hashlib,re
P=Path(__file__).resolve().parent
files=list(P.glob('*.json'));byname={p.name:p for p in files}
for base in [P.parent/'members',P]:
 for p in base.rglob('*.json'):
  for name in [str(p.relative_to(P.parent)),p.relative_to(P.parent).as_posix()]:byname[name]=p
byhash={}
for p in files:byhash.setdefault(hashlib.sha256(p.read_bytes()).hexdigest(),[]).append(p.name)
queue=['q10-only-879-retained.json','q10-c1366-domain.json'];seen=set();links=[];flags=[];unknown=[]
def walk(x,current,path=''):
 if isinstance(x,dict):
  for k,v in x.items():
   if isinstance(v,str)and re.fullmatch('[0-9a-f]{64}',v):
    if k.endswith('.json'):
     if k not in byname: flags.append([current,path+k,'missing_named_file'])
     else:
      actual=hashlib.sha256(byname[k].read_bytes()).hexdigest();links.append([current,k,v==actual]);
      if v!=actual:flags.append([current,k,'hash_mismatch'])
      else:queue.append(k)
    elif v in byhash:
     links.append([current,byhash[v],True]);queue.extend(byhash[v])
    else:unknown.append([current,path+k,v])
   else:walk(v,current,path+k+'.')
 elif isinstance(x,list):
  for i,v in enumerate(x):walk(v,current,path+str(i)+'.')
while queue:
 name=queue.pop()
 if name in seen:continue
 seen.add(name);walk(json.loads(byname[name].read_text()),name)
out=dict(status='integrity_only_not_mathematics',reachable=sorted(seen),links=links,flags=flags,unresolved_hashes=unknown)
(P/'final-source-link-audit.json').write_text(json.dumps(out,indent=2));print('reachable',len(seen),'links',len(links),'flags',flags,'unresolved_hashes',len(unknown))
