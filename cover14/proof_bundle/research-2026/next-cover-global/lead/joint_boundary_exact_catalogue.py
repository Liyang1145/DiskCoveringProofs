"""Stream rationalLPproposals; retangent exactcaps then intervalcertify all966systems."""
import json,time,math,hashlib
from itertools import combinations
from scipy.optimize import brentq
from joint_boundary_exact_cap import verify,P,Q,U,S
D10=json.loads((P/'k10-catalogue-corrected.json').read_text());D11=json.loads((P/'q11-pocket-catalogue.json').read_text());done=0;counts={};start=time.time();r=float(U)
inputs=['joint_boundary_exact_cap.py','JOINT-EXACT-CAP-CONCAVITY.md','BOUNDARY-AREA-PERIMETER-JOINT.md','root_integer_certificate.py','area_safe_certificate.py'];meta={'status':'in_progress','input_hashes':{f:hashlib.sha256((P/f).read_bytes()).hexdigest()for f in inputs}}
(P/'joint-boundary-exact-cap-catalogue-metadata.json').write_text(json.dumps(meta,indent=2))
with(P/'joint-boundary-exact-cap-catalogue.jsonl').open('w',encoding='utf-8')as out:
 while True:
  text=(P/'joint-boundary-catalogue.jsonl').read_text();lines=text.splitlines();rows=[json.loads(x)for x in lines[done:]if x.endswith('}')]
  for row in rows:
   rec=dict(row);fam=row['family'];idx=row['index'];q=int(fam.split('/')[0]);faces=D11['entries'][idx]['faces']if q==11 else D10[fam][idx]['faces'];edges=sorted({tuple(sorted(e))for f in faces for e in combinations(f,2)})
   try:
    ts=rec['rational_angles'][:];mu=float(Q(rec['rational_mu']));y=list(map(float,map(Q,rec['rational_potentials'])))
    for j in range(q):
     def fn(t):
      z=r*math.sin(t/2);bp=r*math.cos(t/2)/math.sqrt(1-z*z);return r*r/2*math.cos(t)+(z*z+mu)*bp-y[j]
     t=0 if fn(0)<=0 else(math.pi if fn(math.pi)>=0 else brentq(fn,0,math.pi));ts[j]=str(max(Q(0),min(Q('3.141592653589'),Q(format(t,'.12f')))))
    rec['rational_angles']=ts;b=verify(q,edges,rec);rec.update(status='excluded'if b.hi<0 else'inconclusive',upper_display=b.hi/S,upper_exact=str(Q(b.hi,S)))
   except Exception as e:rec={'family':fam,'index':idx,'status':'error_not_excluded','error':repr(e)}
   out.write(json.dumps(rec)+'\n');out.flush();done+=1;counts.setdefault(fam,{});counts[fam][rec['status']]=counts[fam].get(rec['status'],0)+1
   if done%50==0:print(done,'seconds',time.time()-start,counts,flush=True)
  source=json.loads((P/'joint-boundary-catalogue-metadata.json').read_text())
  if source['status']=='completed' and done==source['total']:break
  time.sleep(5)
meta.update(status='completed',total=done,counts=counts,seconds=time.time()-start,source_planes_sha256=hashlib.sha256((P/'joint-boundary-catalogue.jsonl').read_bytes()).hexdigest());(P/'joint-boundary-exact-cap-catalogue-metadata.json').write_text(json.dumps(meta,indent=2));print('DONE',done,counts,flush=True)
