from pathlib import Path
import json,time
import interval_cartesian_cancel as f
from interval_joint_patch import I,uf
from cartesian_full_jet import outer_mean,Unsafe
P=Path(__file__).parent;data=json.loads((P/'patch_outer_cartesian_certificate.json').read_text());rows=[];start=time.time()
for row in data['topboxes']:
 box=[I(*q)for q in row['box']];st=f.setup(box);K,fs=st
 try:
  value,grad=outer_mean(box,[dom for fun,dom in fs]);res={'safe':True,'mean_upper':uf(value),'grad':[str(v)for v in grad]}
 except Unsafe as e:res={'safe':False,'reason':str(e)}
 rows.append({'box':row['box'],'old_upper':row['upper'],**res})
out={'scope':'five savedworstboxes; mechanismtest notglobalcert','rows':rows,'seconds':time.time()-start};(P/'full_outer_mean_probe.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
