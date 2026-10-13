"""Hidden bounded process pool for immutable plans. No certificate conclusions.
CLI PLAN OUTPUT_DIR MAX_WORKERS. Each output stem has at most one owned writer.
"""
import subprocess,sys,os,json,time,hashlib
from pathlib import Path
plan=Path(sys.argv[1]);out=Path(sys.argv[2]);limit=int(sys.argv[3]);assert limit>0
out.mkdir(parents=True,exist_ok=True)
assert not (out/'launch.json').exists(),'refuse duplicate pool launch'
raw=plan.read_bytes();ids=[int(b['id'][1:]) for b in json.loads(raw)['branches']]
env=os.environ.copy();env.update(OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',MKL_NUM_THREADS='1')
worker=Path(__file__).with_name('run_planned_branch.py');running={};records=[]
def save():
 tmp=out/'launch.tmp';tmp.write_text(json.dumps(dict(plan_sha256=hashlib.sha256(raw).hexdigest(),pool_pid=os.getpid(),workers=records),indent=2));tmp.replace(out/'launch.json')
while ids or running:
 while ids and len(running)<limit:
  i=ids.pop(0)
  with (out/f'branch-{i}.log').open('a') as stdout,(out/f'branch-{i}.err').open('a') as stderr:
   p=subprocess.Popen([sys.executable,'-B',str(worker),str(plan),str(i),str(out)],stdout=stdout,stderr=stderr,env=env,creationflags=subprocess.CREATE_NO_WINDOW)
  rec=dict(branch=i,pid=p.pid,started=time.time(),exit=None);records.append(rec);running[i]=(p,rec);save()
 time.sleep(2)
 for i,(p,r) in list(running.items()):
  rc=p.poll()
  if rc is not None:r.update(exit=rc,finished=time.time());del running[i];save()
print(json.dumps(dict(exits=[(r['branch'],r['exit']) for r in records])))
