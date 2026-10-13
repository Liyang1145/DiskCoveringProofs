import interval_cancel_fibers as f
import interval_patch_delta as old
import interval_joint_patch as k
import attack_nested_frozen as ref
import math,json,numpy as np
from pathlib import Path
P=Path(__file__).parent;rng=np.random.default_rng(1401);n=0;gap=0
for i in range(250):
 detail=ref.evaluate([rng.uniform(.375,.38),*rng.uniform(.02,.98,3)],True)
 if detail is None:continue
 r,b1,b2,_,_,qa,_=detail['chart'];A=qa*(b1+b2);outer=[k.I(str(x))for x in[r,b1,b2,b1-A]];st=f.setup(outer)
 assert st is not None
 K,fs=st;ww=detail['widths']+[detail['H']]
 # use tinyinterval toabsorbroundedboundarypoint coordinates
 outer=[k.I(float(x.a)-1e-12,float(x.b)+1e-12)for x in outer];K,fs=f.setup(outer);total=K
 for (fun,_),x in zip(fs,ww):
  y=fun(k.I(x-1e-12,x+1e-12));assert y is not None;total+=y
 assert k.lf(total)<=detail['value']<=k.uf(total),(total,detail['value'])
 n+=1
out={'points':n,'contains_independent_objective':True,'scope':'interfacecalibrationonly'};(P/'cancel_fibers_control.json').write_text(json.dumps(out,indent=2));print(out)
