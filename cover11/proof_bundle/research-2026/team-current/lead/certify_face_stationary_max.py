"""Exact decimal witness: legal face-arc strict interior local maximum; no claim about global arc maximum."""
from pathlib import Path
import json,hashlib
import face_second_jet as f
from interval_joint_patch import I,iv,lf,uf
P=Path(__file__).parent;r,b1,b2=map(I,['.377','1.008','1.001']);s=iv.sqrt(1-r*r)
left=f.objective([r,b1,b2,I('-.32')],0);right=f.objective([r,b1,b2,I('-.31')],0);assert left.d.a>0 and right.d.b<0
rows=[]
for j in range(100):
 d=I((I('-.32')+I(j)/10000).a,(I('-.32')+I(j+1)/10000).b)
 H=2*r*iv.sin(2*b1-d);cap2=2*r*iv.sin(2*b2+d)
 norm=H*H-2*s*iv.cos(d)*H+2*r*(1-r)
 assert H.a>0 and (cap2-H).a>0 and norm.b<0 and (b1-d).a>0 and (b2+d).a>0
 v=H*iv.cos(d);t=H*iv.sin(d)
 # independent Cartesian disk2/norm margins (face1 exact param equation)
 disk2=(v-r*iv.sin(2*b2))**2+(t-r*iv.cos(2*b2))**2-r*r
 norm2=(v-s)**2+t*t-(1-r)**2
 assert disk2.b<0 and norm2.b<0
 obj=f.objective([r,b1,b2,d],0);assert obj.h.b<0
 rows.append({'delta':str(d),'Gsecond':str(obj.h),'disk2':str(disk2),'norm':str(norm2)})
out={'scope':'r=.377,b1=1.008,b2=1.001,face1delta[-.32,-.31]; strictinterior LOCALarcmaxexistsuniquely; no globalarcmaxcomparison','left_derivative':str(left.d),'right_derivative':str(right.d),'upper_second':max(float(iv.mpf(row['Gsecond'][1:-1].split(',')[1]).b)for row in rows),'pieces':rows,'coefficient_sha256':hashlib.sha256((P/'joint_nested_frozen.json').read_bytes()).hexdigest(),'source_sha256':{n:hashlib.sha256((P/n).read_bytes()).hexdigest()for n in ['face_second_jet.py','certify_face_stationary_max.py']}}
(P/'face_stationary_max_certificate.json').write_text(json.dumps(out,indent=2));print({k:v for k,v in out.items()if k!='pieces'})
