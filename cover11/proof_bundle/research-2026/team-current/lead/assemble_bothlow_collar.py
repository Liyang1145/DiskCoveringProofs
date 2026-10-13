from pathlib import Path
import json,hashlib
from mpmath import iv
iv.dps=40;P=Path(__file__).parent;f=P/'joint_nested_frozen.json';digest=hashlib.sha256(f.read_bytes()).hexdigest();z=[iv.mpf(f'{x:.9f}')for x in json.loads(f.read_text())['z']];assert len(z)==121 and all(x==0 for x in z[50:73]);const=iv.pi*(sum(z[:9])+2*sum(z[9:11])-sum(z[112:]));ids=[i for i in range(29)if i not in[1,2,12,13,21,22,23]];folder=P.parent/'cline2-coupled-factors/out'/('r15_'+digest[:12]);rest=iv.mpf(0)
for i in ids:
 files=list(folder.glob(f'*bound_{i:02d}.json'));assert len(files)==1;q=json.loads(files[0].read_text());assert q['coefficient_sha256']==digest;rest+=iv.mpf(q['upper'])
rows=[]
for name in ['coincident_collar_certificate.json','norm_collar_certificate.json']:
 q=json.loads((P/name).read_text());assert q['live']==0
 for n,h in q['source_sha256'].items():assert hashlib.sha256((P/n).read_bytes()).hexdigest()==h,(name,n)
 u=iv.mpf(str(q['terminal']));total=const+rest+u;assert total.b<iv.pi.a
 rows.append({'file':name,'sha256':hashlib.sha256((P/name).read_bytes()).hexdigest(),'upper':str(u),'assembly':str(total),'margin':str(iv.pi-total)})
out={'scope':'bothlowC849flatpatch alpha2pi, |b1+b2−pi/2|<=.005, r[.379,.37999], excluded conditionalonC871boundaryreduction/C872widthendpoint/C850floor. Notglobalsharpcoverproof.','coefficient_sha256':digest,'constant_plus22':str(const+rest),'components':rows};(P/'bothlow_collar_assembly.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
