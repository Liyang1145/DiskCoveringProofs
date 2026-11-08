import os,subprocess,json
from pathlib import Path
base=Path(__file__).resolve().parent
repo=base.parent/'git-cache'; target=base/'native-recovered'; rev='6869e8ad9a92693e88b891e74ec3e10f703b4146'
env=dict(os.environ,GIT_NO_LAZY_FETCH='1')
def run(*args): return subprocess.run(['git',f'--git-dir={repo}',*args],env=env,capture_output=True)
entries=run('ls-tree','-r',rev,'cover26').stdout.decode().splitlines()
selected=[]
for row in entries:
 meta,path=row.split('\t',1); oid=meta.split()[2]; name=path.lower()
 if (name.endswith('.md') and any(t in name for t in ('candidate','cover','radius','proof','upper','status'))) or any(t in name for t in ('same_root_cover.py','contact_root.py','same-root-cover','positive-stress','candidate-transport','n26-sharp-radius')):
  selected.append((path,oid))
found=[]; missing=[]
for path,oid in selected:
 size=run('cat-file','-s',oid)
 if size.returncode: missing.append(path); continue
 blob=run('cat-file','blob',oid)
 if blob.returncode or len(blob.stdout)!=int(size.stdout): raise RuntimeError(path)
 dst=target/Path(path); dst.parent.mkdir(parents=True,exist_ok=True); dst.write_bytes(blob.stdout)
 found.append({'path':path,'git_blob':oid,'bytes':len(blob.stdout)})
(target/'inventory.json').write_text(json.dumps({'commit':rev,'present':found,'missing':missing},indent=2),encoding='utf8')
print('selected',len(selected),'present',len(found),'missing',len(missing))
print('\n'.join(x['path'] for x in found))
