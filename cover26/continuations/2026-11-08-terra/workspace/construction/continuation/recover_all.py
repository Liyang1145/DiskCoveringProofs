import os, subprocess, json, hashlib
from pathlib import Path
root=Path(__file__).resolve().parent; repo=root.parent.parent/'git-cache'; env=dict(os.environ,GIT_NO_LAZY_FETCH='1');
def run(*x): return subprocess.run(['git',f'--git-dir={repo}',*x],capture_output=True,env=env)
objects=run('cat-file','--batch-all-objects','--batch-check=%(objectname) %(objecttype) %(objectsize)').stdout.decode().splitlines()
commits=[x.split()[0] for x in objects if x.split()[1]=='commit']; blobs={x.split()[0]:int(x.split()[2]) for x in objects if x.split()[1]=='blob'}
byoid={}; trees=[]
for commit in commits:
 tree=run('ls-tree','-r',commit,'cover26')
 if tree.returncode: trees.append({'commit':commit,'ok':False,'error':tree.stderr.decode(errors='replace')}); continue
 entries=tree.stdout.decode('utf8').splitlines(); trees.append({'commit':commit,'ok':True,'paths':len(entries)})
 for entry in entries:
  meta,path=entry.split('\t',1); oid=meta.split()[2]
  if oid in blobs:
   d=byoid.setdefault(oid,{'paths':set(),'commits':set()}); d['paths'].add(path); d['commits'].add(commit)
found=[]
for oid,d in byoid.items():
 s=run('cat-file','-s',oid)
 if s.returncode: continue
 b=run('cat-file','blob',oid)
 if b.returncode or len(b.stdout)!=int(s.stdout): raise RuntimeError(oid)
 paths=sorted(d['paths']); path=paths[0]; name=Path(path).name
 dst=root/'recovered'/f'{oid}_{name}'; dst.parent.mkdir(parents=True,exist_ok=True); dst.write_bytes(b.stdout)
 found.append({'oid':oid,'sha256':hashlib.sha256(b.stdout).hexdigest(),'size':len(b.stdout),'paths':paths,'commits':sorted(d['commits']),'file':str(dst.relative_to(root))})
(root/'all-commits-inventory.json').write_text(json.dumps({'trees':trees,'records':found},indent=2),encoding='utf8')
print('tree results:',trees); print('unique cover26 available blobs',len(found))
for x in found: print(x['size'], x['oid'],x['paths'][0])
