from ridge_outer_jet import mean,parts,Unsafe
from interval_joint_patch import I,uf
from interval_hub_boundary import setup
import interval_ridge_only as nat
import json
from pathlib import Path
P=Path(__file__).parent
boxes=json.loads((P/'patch_outer_hub_boundary_certificate.json').read_text())['topboxes'];out=[]
for row in boxes:
 x=[I(*p) for p in row['box']];st=setup(x)
 if st is None:continue
 K,ws,_=st
 try:
  v,g=mean(x,[d for f,d in ws]);old=nat.bound(x)['upper'];out.append({'box':row['box'],'mean':uf(v),'natural':old,'gradient':[str(a)for a in g]})
 except Unsafe as e:out.append({'error':str(e)})
print(out);(P/'ridge_mean_probe.json').write_text(json.dumps(out,indent=2))
