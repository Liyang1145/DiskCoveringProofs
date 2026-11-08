import subprocess,os,json,hashlib
from pathlib import Path
root=Path(__file__).resolve().parent; repo=root.parent.parent/'git-cache'; env=dict(os.environ,GIT_NO_LAZY_FETCH='1')
def run(*args): return subprocess.run(['git',f'--git-dir={repo}',*args],capture_output=True,env=env)
rows=run('cat-file','--batch-all-objects','--batch-check=%(objectname) %(objecttype) %(objectsize)').stdout.decode().splitlines()
need={'e555cb470ef4a3a8c5167f95307e7b0220c8b77a0fe7b435010220450eb44ef7','598d65cbc3d839780e3f6b8dbdc3cd36331a391f716eacc1cae83144903b2794'}
results=[]
for line in rows:
 oid,kind,size=line.split(); size=int(size)
 if kind!='blob':continue
 z=run('cat-file','blob',oid)
 if z.returncode or len(z.stdout)!=size:raise RuntimeError(oid)
 h=hashlib.sha256(z.stdout).hexdigest()
 matches=[t.decode() for t in (b'0.234700090400448',b'0.23470009',b'134rod',b'ROOT-CERTIFICATE',b'candidate geometry') if t in z.stdout]
 if matches or h in need: results.append({'oid':oid,'sha256':h,'bytes':size,'matches':matches,'required_sha':h in need})
(root/'blob-content-scan.json').write_text(json.dumps(results,indent=2),encoding='utf8')
print(json.dumps(results,indent=2))
