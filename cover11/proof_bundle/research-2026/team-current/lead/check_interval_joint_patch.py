from pathlib import Path
import json,math,numpy as np
import interval_joint_patch as kern
import attack_nested_frozen as ref
P=Path(__file__).parent
rng=np.random.default_rng(1301);n=0;err=0
for _ in range(2500):
 y=[rng.uniform(.375,.38),*rng.uniform(0,1,3)];r,q1,q2,qA=y;bc=math.acos(r);b1=bc*(.5+.5*q1);b2=bc*(.5+.5*q2);W1,W3=ref.width(r,b1),ref.width(r,b2);A=qA*(b1+b2);B=b1+b2-A;s=math.sqrt(1-r*r);de=b1-A;dis=s*s*math.cos(de)**2-2*r*(1-r)
 if dis<0 or min(W1,W3)<ref.g:continue
 lo=max(2*r*abs(math.sin(de)),s*math.cos(de)-math.sqrt(dis));hi=min(2*r*math.sin(b1+A),2*r*math.sin(b2+B),s*math.cos(de)+math.sqrt(dis))
 if lo>hi:continue
 ww1,ww3=rng.uniform(ref.g,W1),rng.uniform(ref.g,W3);H=rng.uniform(lo,hi);box=[r,b1,b2,A,ww1,ww3,H]
 chart=[r,b1,b2,(ww1-ref.g)/(W1-ref.g),(ww3-ref.g)/(W3-ref.g),qA,(H-lo)/(hi-lo)]
 xx=ref.ns['chart'](chart)
 if xx is None:continue
 direct=ref.ns['reduced'](xx);vv=kern.evaluate([kern.I(str(t))for t in box]);assert vv is not None,(box,direct)
 gap=max(kern.lf(vv)-direct,direct-kern.uf(vv),0);err=max(err,gap);assert gap<2e-10,(box,vv,direct)
 # slightlythick boxmustcontainfloatingvaluewellwithinerror
 vb=kern.evaluate([kern.I(t-1e-10,t+1e-10)for t in box]);assert vb is not None and kern.lf(vb)<direct<kern.uf(vb)
 n+=1
out={'points':n,'max_float_point_discrepancy':err,'thickboxes_contain':True,'scope':'calibration not continuum certificate'};(P/'interval_joint_control.json').write_text(json.dumps(out,indent=2));print(out)
