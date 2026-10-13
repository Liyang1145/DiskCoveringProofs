from pathlib import Path
import json,numpy as np,hashlib
P=Path(__file__).parent;s=(P/'check_joint_reduced.py').read_text();ns={'__file__':str(P/'check_joint_reduced.py')};exec(s.split("if __name__=='__main__':")[0],ns)
f=P/'joint_nested_frozen.json';z=np.array(json.loads(f.read_text())['z']);ns['z']=z
rng=np.random.default_rng(1515);n=0;err=0
for _ in range(1500):
 x=np.array([rng.uniform(l,h)for l,h in ns['ns']['bounds']])
 if ns['patch'](x) is None:continue
 v,m=ns['catom'](x);e=abs(ns['reduced'](x)-(v+m@z));err=max(err,e);assert e<1e-10;n+=1
out={'coefficient_sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'points':n,'max_error':err,'scope':'current7factorinterfacecalibration; analyticidentityfromsameatomexpansion'};(P/'current_seven_split_control.json').write_text(json.dumps(out,indent=2));print(out)
