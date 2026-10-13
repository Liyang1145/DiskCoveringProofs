from pathlib import Path
import json,hashlib
from mpmath import iv
iv.dps=40;P=Path(__file__).parent;f=P/'joint_nested_frozen.json';digest=hashlib.sha256(f.read_bytes()).hexdigest();z=[iv.mpf(f'{x:.9f}')for x in json.loads(f.read_text())['z']];assert len(z)==121 and all(x==0 for x in z[50:73]);const=iv.pi*(sum(z[:9])+2*sum(z[9:11])-sum(z[112:]));ids=[i for i in range(29)if i not in[1,2,12,13,21,22,23]];folder=P.parent/'cline2-coupled-factors/out'/('r15_'+digest[:12]);rest=iv.mpf(0)
for i in ids:
 files=list(folder.glob(f'*bound_{i:02d}.json'));assert len(files)==1;q=json.loads(files[0].read_text());assert q['coefficient_sha256']==digest;rest+=iv.mpf(q['upper'])
rows=[]
for file in ['ridge_tangent_certificate.json','patch_outer_norm_boundary_certificate.json','stationary_face_bound_certificate.json']:
 q=json.loads((P/file).read_text());assert q['coefficient_sha256']==digest
 if file.startswith('ridge'):assert all(x['live']==0 for x in q['components']);u=iv.mpf(q['upper'])
 elif file.startswith('patch'):assert q['liveboxes']==0 and not q['budget_ended'];u=iv.mpf(q['upper'])
 else:assert q['live']==0;u=iv.mpf(q['terminal'])
 if 'source_sha256'in q:
  for name,h in q['source_sha256'].items():assert hashlib.sha256((P/name).read_bytes()).hexdigest()==h
 total=const+rest+u;assert total.b<iv.pi.a
 rows.append({'file':file,'sha256':hashlib.sha256((P/file).read_bytes()).hexdigest(),'upper':str(u),'assembly':str(total),'margin':str(iv.pi-total)})
out={'scope':'C861+C863+C869+stationary certificate implies ALL HIGHBEARING flatq0alpha2pi patches infeasible, actualr[.379,.37999]. Not minb<1 or globalcoveroptimum. Endpoint theorem required.','coefficient_sha256':digest,'constant_plus22':str(const+rest),'components':rows}
(P/'highbearing_boundary_assembly.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
