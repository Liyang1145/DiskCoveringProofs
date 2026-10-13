"""Sequential source replay; no optimization. Keep bulk output in logs."""
from pathlib import Path
import subprocess,sys,time,json,hashlib
P=Path(__file__).resolve().parent
jobs=[('check_shared_dual_symbolic.py',[]),('check_shared_moment_dense_symbolic.py',[]),('check_q0_closure_symbolic.py',[]),('check_q0_moment_symbolic.py',[]),('check_quadratic_support.py',[]),('certify_shared_moments_dense.py',['0','4']),('certify_shared_moments_dense.py',['2','4']),('certify_q0_closure.py',['0','3']),('certify_q0_moments.py',['0','2'])]
rows=[]
for name,args in jobs:
 t=time.time(); tag=name.removesuffix('.py')+'_'+('_'.join(args) or 'control')
 with (P/(tag+'_r23.log')).open('w',encoding='utf8') as f:
  p=subprocess.run([sys.executable,'-B',str(P/name),*args],stdout=f,stderr=subprocess.STDOUT)
 row={'script':name,'args':args,'returncode':p.returncode,'seconds':time.time()-t,'sha256':hashlib.sha256((P/name).read_bytes()).hexdigest(),'log':str(P/(tag+'_r23.log'))};rows.append(row)
 (P/'upstream_replay_r23.json').write_text(json.dumps(rows,indent=2),encoding='utf8')
 print(name,args,p.returncode,round(row['seconds'],2),flush=True)
 if p.returncode:raise SystemExit(p.returncode)
