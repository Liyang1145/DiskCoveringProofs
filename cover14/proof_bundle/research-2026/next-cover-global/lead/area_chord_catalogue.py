"""Bounded one-pass1588retainedgraphs, chordaffineconstraint, <=600iterations each."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
import json,time,hashlib
from itertools import combinations
from area_chord_probe import solve_cert,P,Q
D10=json.loads((P/'k10-catalogue-corrected.json').read_text());D11=json.loads((P/'q11-pocket-catalogue.json').read_text());saved=[json.loads(x)for x in(P/'area-safe-catalogue.jsonl').read_text().splitlines()];remaining={(x['family'],x['index'])for x in json.loads((P/'area-sharp-cap.json').read_text())['runs']if x['status']=='inconclusive'}
inputs=['area_chord_probe.py','area_safe_certificate.py','root_integer_certificate.py','area-safe-catalogue.jsonl','area-sharp-cap.json','k10-catalogue-corrected.json','q11-pocket-catalogue.json','BOUNDARY-CHORD-ENVELOPE.md'];meta={'status':'in_progress','input_hashes':{f:hashlib.sha256((P/f).read_bytes()).hexdigest()for f in inputs}};counts={};start=time.time();done=0
(P/'area-chord-catalogue-metadata.json').write_text(json.dumps(meta,indent=2))
with(P/'area-chord-catalogue.jsonl').open('w',encoding='utf-8')as fp:
 for row in saved:
  fam=row['family'];idx=row['index']
  if(fam,idx)not in remaining:continue
  q=int(fam.split('/')[0]);n=q+int(fam.split('/')[1]);faces=D11['entries'][idx]['faces']if q==11 else D10[fam][idx]['faces'];edges=sorted({tuple(sorted(e))for f in faces for e in combinations(f,2)})
  try:rec=solve_cert(n,q,edges,list(map(Q,row['rational_angles'])))
  except Exception as e:rec={'status':'error_not_excluded','error':repr(e)}
  rec.update(family=fam,index=idx);fp.write(json.dumps(rec)+'\n');fp.flush();done+=1;counts.setdefault(fam,{});counts[fam][rec['status']]=counts[fam].get(rec['status'],0)+1
  if done%100==0:print(done,'seconds',round(time.time()-start,2),counts,flush=True)
meta.update(status='completed',total=done,counts=counts,seconds=time.time()-start);(P/'area-chord-catalogue-metadata.json').write_text(json.dumps(meta,indent=2));print('DONE',done,meta['seconds'],counts,flush=True)
