"""One729survivorpass: 200numericboxsplits/facepropose bestface; <=2000exactintervalsplitsverify."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
import json,time,hashlib,math
from itertools import combinations
from fractions import Fraction as Q
from face_deficit_probe import solve
from face_deficit_certificate import certify,P,sc,costerm
D10=json.loads((P/'k10-catalogue-corrected.json').read_text());D11=json.loads((P/'q11-pocket-catalogue.json').read_text());rows=[json.loads(x)for x in(P/'joint-innernorm-catalogue.jsonl').read_text().splitlines()];r=.33173203427623414;a=r*r;start=time.time();done=0;counts={}
inputs=['face_deficit_certificate.py','face_deficit_probe.py','joint_innernorm_probe.py','RADIUS-DEFICIT-LEMMA.md','FACE-ANGLE-INTERFACE-DRAFT.md','joint-innernorm-catalogue.jsonl','joint-innernorm-retained.json'];meta={'status':'in_progress','input_hashes':{f:hashlib.sha256((P/f).read_bytes()).hexdigest()for f in inputs}}
(P/'face-deficit-catalogue-metadata.json').write_text(json.dumps(meta,indent=2))
with(P/'face-deficit-catalogue.jsonl').open('w')as fp:
 for row in rows:
  if row['status']!='inconclusive':continue
  fam=row['family'];idx=row['index'];q=int(fam.split('/')[0]);faces=D11['entries'][idx]['faces']if q==11 else D10[fam][idx]['faces'];edges=sorted({tuple(sorted(e))for f in faces for e in combinations(f,2)});y=list(map(float,map(Q,row['rational_potentials'])));t=list(map(float,map(Q,row['rational_angles'])));cnt={e:sum(all(v in f for v in e)for f in faces)for e in edges};tests=[]
  for j,f in enumerate(faces):
   ee=[tuple(sorted(e))for e in combinations(f,2)]
   if not all(cnt[e]==2 for e in ee):continue
   pot=[sum(y[v]for v in e)for e in ee];old=0
   for e,pp in zip(ee,pot):
    x=t[q+edges.index(e)];old+=a*(math.sin(x)-x*math.cos(x))+math.pi*max(0,a*math.cos(x)-pp)
   new=solve(pot,200);tests.append((row['upper_display']+new-old,j))
  best=min(tests,default=(float('inf'),-1));rec={'family':fam,'index':idx,'status':'inconclusive','numeric_best_upper':best[0],'numeric_face':best[1]}
  if best[0]<0:
   try:rec=certify(q,edges,faces,row,best[1],2000)
   except Exception as e:rec.update(status='error_not_excluded',error=repr(e))
  fp.write(json.dumps(rec)+'\n');fp.flush();done+=1;counts.setdefault(fam,{});counts[fam][rec['status']]=counts[fam].get(rec['status'],0)+1
  if done%50==0:print(done,'seconds',time.time()-start,counts,flush=True);sc.cache_clear();costerm.cache_clear()
meta.update(status='completed',total=done,seconds=time.time()-start,counts=counts);(P/'face-deficit-catalogue-metadata.json').write_text(json.dumps(meta,indent=2));print('DONE',done,counts,flush=True)
