"""Final q1(5,7) source replay; no optimizer. Logs kept separately."""
from pathlib import Path
import subprocess,sys,json,time,hashlib
P=Path(__file__).resolve().parent
jobs=[('certify_shared_factors.py',[str(s),'3']) for s in range(4)]+[('check_compatible_fraction.py',[]),('check_degree3_fraction.py',[]),('check_degree4_triple_fraction.py',[])]
rows=[]
for name,args in jobs:
 t=time.time();tag=name.removesuffix('.py')+'_'+('_'.join(args) or 'control')+'_final'
 with (P/(tag+'.log')).open('w',encoding='utf8') as f:
  p=subprocess.run([sys.executable,'-B',str(P/name),*args],stdout=f,stderr=subprocess.STDOUT)
 rows.append(dict(script=name,args=args,returncode=p.returncode,seconds=time.time()-t,sha256=hashlib.sha256((P/name).read_bytes()).hexdigest(),log=tag+'.log'))
 (P/'q1_final_replay.json').write_text(json.dumps(rows,indent=2),encoding='utf8')
 print(name,args,p.returncode,flush=True)
 if p.returncode:raise SystemExit(p.returncode)
