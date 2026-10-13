import interval_monotone_h_fibers as f
import interval_joint_patch as k
import attack_nested_frozen as ref
import numpy as np,json
rng=np.random.default_rng(1500);n=0;calls=0
for i in range(80):
 detail=ref.evaluate([rng.uniform(.375,.38),*rng.uniform(.05,.95,3)],True)
 if detail is None:continue
 r,b1,b2,_,_,qa,_=detail['chart'];A=qa*(b1+b2);outer=[k.I(x-1e-10,x+1e-10)for x in [r,b1,b2,b1-A]]
 row=f.bound(outer,maxeval=63);assert row is not None and row['upper']>=detail['value'],(row,detail)
 n+=1
out={'samples':n,'containment':True,'stats':f.stats,'scope':'calibrationonly'};(k.P/'monotone_h_control.json').write_text(json.dumps(out,indent=2));print(out)
