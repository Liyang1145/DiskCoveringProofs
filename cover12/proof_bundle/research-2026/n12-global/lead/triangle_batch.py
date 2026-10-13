"""Bounded four remaining positive triangle-block classes; output proposals and
strict cert failures separately. No domain enlargement or optimization retry."""
from pathlib import Path
import subprocess,sys,json
P=Path(__file__).resolve().parent
rows=[]
for name,kappa in [('117','1/20'),('126','1/20'),('135','1/20'),('144','1/20')]:
 args=[sys.executable,'-B',str(P/'network_minimax.py'),','.join(name)]
 r=subprocess.run(args,capture_output=True,text=True,timeout=120)
 (P.parent/'evidence'/('network-minimax-'+name+'.log')).write_text(r.stdout+r.stderr)
 if r.returncode:rows.append({'type':name,'stage':'scout','exit':r.returncode});continue
 r=subprocess.run([sys.executable,'-B',str(P/'network_interval_certificate.py'),name,kappa],capture_output=True,text=True,timeout=120)
 (P.parent/'evidence'/('network-certified-'+name+'.log')).write_text(r.stdout+r.stderr)
 rows.append({'type':name,'stage':'certificate','exit':r.returncode})
 print(rows[-1],flush=True)
(P.parent/'evidence'/'triangle-batch.json').write_text(json.dumps(rows,indent=2))
