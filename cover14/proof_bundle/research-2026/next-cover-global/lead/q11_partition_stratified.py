"""16 stratified onechord controls; atmost31nodes each; proposal/evidence unregistered."""
from pathlib import Path
import json,subprocess,sys
P=Path(__file__).resolve().parent;rows=json.loads((P/'q11-onechord-flow-proposals.json').read_text())['runs'];rows=sorted(rows,key=lambda r:r['robust_value']);ids=[rows[round(j*(len(rows)-1)/15)]['index']for j in range(16)];print('indices',ids,flush=True)
for idx in ids:
 subprocess.run([sys.executable,'-B',str(P/'q11_polytope_partition_probe.py'),str(idx)],check=True)
print('DONE STRATIFIED',ids,flush=True)
