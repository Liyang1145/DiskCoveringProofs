import interval_height_fibers as f
import interval_joint_patch as k
import attack_nested_frozen as ref
import numpy as np,json,math
rng=np.random.default_rng(1501);n=0
for i in range(150):
 d=ref.evaluate([rng.uniform(.375,.38),*rng.uniform(.02,.98,3)],True)
 if d is None:continue
 r,b1,b2,_,_,qa,_=d['chart'];delta=b1-qa*(b1+b2);eps=delta-(b1-b2);u=math.asin(d['H']/(2*r));st=f.setup([k.I(x-1e-11,x+1e-11)for x in[r,b1,b2,u]])
 assert st is not None
 K,fs=st;v=K
 for (fun,dom),x in zip(fs,d['widths']+[eps]):
  assert dom[0]-1e-10<=x<=dom[1]+1e-10,(dom,x)
  val=fun(k.I(x-1e-11,x+1e-11));assert val is not None;v+=val
 assert k.lf(v)<=d['value']<=k.uf(v),(v,d['value'])
 n+=1
out={'points':n,'containment':True,'scope':'calibrationonly'};(k.P/'height_fibers_control.json').write_text(json.dumps(out,indent=2));print(out)
