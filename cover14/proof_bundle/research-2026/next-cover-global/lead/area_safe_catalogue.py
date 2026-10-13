"""One bounded pass through corrected q10(1000) and retained q11(1042).
At most400 optimizeriterations/graph; any rational dual proposal certified separately.
Numeric failure never excludes graph. No repeatedprecision/grids; 1 pass only.
"""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
import json,time,hashlib
from itertools import combinations
from area_safe_probe import solve,P
from area_safe_certificate import certify
D10=json.loads((P/'k10-catalogue-corrected.json').read_text());D11=json.loads((P/'q11-pocket-catalogue.json').read_text());keep=json.loads((P/'q11-double-chord-pruning.json').read_text())['retained_indices']
inputs=['k10-catalogue-corrected.json','q11-pocket-catalogue.json','q11-double-chord-pruning.json','area_safe_probe.py','area_safe_certificate.py','root_integer_certificate.py','AREA-SAFE-RELAXATION.md']
meta={'status':'in_progress','scope':'cover-to-angle necessary relaxation atU, not optimum theorem','input_hashes':{f:hashlib.sha256((P/f).read_bytes()).hexdigest()for f in inputs}}
(P/'area-safe-catalogue-metadata.json').write_text(json.dumps(meta,indent=2))
tasks=[]
for key in ['10/3','10/4']:
 for i,e in enumerate(D10[key]):tasks.append((key,i,e['faces'],10+e['m'],10))
for i in keep:tasks.append(('11/3',i,D11['entries'][i]['faces'],14,11))
counts={};start=time.time();out=P/'area-safe-catalogue.jsonl'
with out.open('w',encoding='utf-8')as fp:
 for k,(family,idx,faces,n,q)in enumerate(tasks):
  edges=sorted({tuple(sorted(e))for f in faces for e in combinations(f,2)})
  try:
   numeric=solve(n,q,edges,.33173203427623414)
   rec=certify(n,q,edges,numeric['angles'],idx)
   rec['numeric_success']=numeric['success'];rec['numeric_eq_residual']=numeric['eqresid'];rec['numeric_bound']=numeric['area']
  except Exception as e:
   rec={'index':idx,'status':'error_not_excluded','error':repr(e)}
  rec['family']=family;counts.setdefault(family,{});counts[family][rec['status']]=counts[family].get(rec['status'],0)+1
  fp.write(json.dumps(rec)+'\n');fp.flush()
  if (k+1)%100==0:print(k+1,'of',len(tasks),'seconds',round(time.time()-start,2),'counts',counts,flush=True)
meta.update(status='completed',counts=counts,total=len(tasks),seconds=time.time()-start)
(P/'area-safe-catalogue-metadata.json').write_text(json.dumps(meta,indent=2));print('DONE',meta['seconds'],counts,flush=True)
