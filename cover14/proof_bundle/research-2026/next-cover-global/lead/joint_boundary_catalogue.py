"""One bounded966graph pass;81angle LP samples propose, analytic concavetangents certify."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
import json,time,hashlib
from itertools import combinations
from joint_boundary_probe import solve_cert,P
D10=json.loads((P/'k10-catalogue-corrected.json').read_text());D11=json.loads((P/'q11-pocket-catalogue.json').read_text());rows=json.loads((P/'innernorm-retained.json').read_text())['retained'];counts={};start=time.time();done=0
inputs=['joint_boundary_probe.py','area_safe_certificate.py','root_integer_certificate.py','innernorm-retained.json','k10-catalogue-corrected.json','q11-pocket-catalogue.json','BOUNDARY-AREA-PERIMETER-JOINT.md'];meta={'status':'in_progress','input_hashes':{f:hashlib.sha256((P/f).read_bytes()).hexdigest()for f in inputs}}
(P/'joint-boundary-catalogue-metadata.json').write_text(json.dumps(meta,indent=2))
with(P/'joint-boundary-catalogue.jsonl').open('w',encoding='utf-8')as fp:
 for row in rows:
  fam=row['family'];idx=row['index'];q=int(fam.split('/')[0]);faces=D11['entries'][idx]['faces']if q==11 else D10[fam][idx]['faces'];edges=sorted({tuple(sorted(e))for f in faces for e in combinations(f,2)})
  try:rec=solve_cert(q,edges)
  except Exception as e:rec={'status':'error_not_excluded','error':repr(e)}
  rec.update(family=fam,index=idx);fp.write(json.dumps(rec)+'\n');fp.flush();done+=1;counts.setdefault(fam,{});counts[fam][rec['status']]=counts[fam].get(rec['status'],0)+1
  if done%50==0:print(done,'seconds',round(time.time()-start,2),counts,flush=True)
meta.update(status='completed',total=done,counts=counts,seconds=time.time()-start);(P/'joint-boundary-catalogue-metadata.json').write_text(json.dumps(meta,indent=2));print('DONE',done,meta['seconds'],counts,flush=True)
