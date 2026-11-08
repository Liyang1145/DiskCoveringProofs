from pathlib import Path
import json
import numpy as np
from scipy.optimize import milp,LinearConstraint,Bounds
from scipy.sparse import csc_matrix
p=Path(__file__).resolve().parent;d=json.loads((p/'five_ring_exact.json').read_text()); masks=[int(v,16) for v in d['masks']]; rows=[];cols=[]
for j,z in enumerate(masks):
 while z:
  b=z&-z; rows.append(b.bit_length()-1);cols.append(j);z-=b
A=csc_matrix((np.ones(len(rows)),(rows,cols)),shape=(len(d['points']),len(masks))); A.indices=A.indices.astype(np.int32);A.indptr=A.indptr.astype(np.int32)
x=milp(np.ones(len(masks)),integrality=np.ones(len(masks)),bounds=Bounds(0,1),constraints=LinearConstraint(A,1,np.inf),options={'time_limit':60})
print('milp',x.status,x.fun,getattr(x,'mip_dual_bound',None));assert x.x is not None
chosen=[d['masks'][i] for i,y in enumerate(x.x) if y>.5]
union=0
for v in chosen:union|=int(v,16)
assert union==(1<<len(d['points']))-1
out={'source':'five_ring_exact.json','radius':d['radius'],'selected_masks':chosen,'selected_witnesses':[d['mask_witnesses'][v] for v in chosen],'geometry_check':'Run verify_finite_cover.py; numerical MILP is used only to discover these centers.'}
(p/'finite_cover_23.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
print('candidate count',len(chosen))
