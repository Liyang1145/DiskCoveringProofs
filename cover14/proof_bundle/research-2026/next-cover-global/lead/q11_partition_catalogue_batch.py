"""One bounded31additionalnode pass perremainingq11 system; two independentreplays for completedtrees."""
from pathlib import Path
import json,subprocess,sys,time
P=Path(__file__).resolve().parent;start=time.time();rows=json.loads((P/'q10-single-type-retained.json').read_text())['retained'];out=[]
for r in rows:
 if r['family']!='11/3':continue
 idx=r['index'];src=P/f'q11-polytope-partition-{idx}.json'
 if not src.exists()or json.loads(src.read_text())['pending']:subprocess.run([sys.executable,'-B',str(P/'q11_polytope_partition_probe.py'),str(idx)],check=True)
 a=json.loads(src.read_text());rec={'index':idx,'processed':a['processed'],'pending':len(a['pending'])}
 if not a['pending']:
  subprocess.run([sys.executable,'-B',str(P/'q11_split_inductive_audit.py'),str(idx)],check=True);subprocess.run([sys.executable,'-B',str(P/'q11_partition_coverage_audit.py'),str(idx)],check=True);rec['certified']=True
 else:rec['certified']=False
 out.append(rec);(P/'q11-partition-catalogue-batch.json').write_text(json.dumps({'status':'bounded_catalogue_pass','runs':out,'seconds':time.time()-start},indent=2));print('BATCH',len(out),idx,rec,flush=True)
