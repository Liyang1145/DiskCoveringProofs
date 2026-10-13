import patch_cancel_jet as sj
import attack_nested_frozen as ref
from pathlib import Path
import numpy as np,math,json
rng=np.random.default_rng(1400);n=0;err=0;de=0;P=Path(__file__).parent
for trial in range(150):
 y=[rng.uniform(.375,.38),*rng.uniform(.03,.97,3)];detail=ref.evaluate(y,True)
 if detail is None:continue
 r,b1,b2,_,_,qa,_=detail['chart'];A=qa*(b1+b2);w1,w3=detail['widths'];H=detail['H'];x=np.array([r,b1,b2,b1-A,w1,w3,H]);f=sj.objective([sj.I(str(v))for v in x]);value=float(f.v.mid);err=max(err,abs(value-detail['value']));assert err<1e-10
 for i in range(7):
  h=2e-6;xp=x.copy();xm=x.copy();xp[i]+=h;xm[i]-=h
  fd=(float(sj.objective([sj.I(str(v))for v in xp]).v.mid)-float(sj.objective([sj.I(str(v))for v in xm]).v.mid))/(2*h)
  dg=float(f.d[i].mid);de=max(de,abs(fd-dg));assert abs(fd-dg)<1e-6,(i,fd,dg)
 box=[sj.I(v-1e-7,v+1e-7)for v in x];up,_,_=sj.mean_bound(box);assert up>=value
 n+=1
out={'samples':n,'maxvalueerror':err,'maxgradientFDerror':de,'scope':'calibrationonly; no domaincertificate'};(P/'cancel_jet_control.json').write_text(json.dumps(out,indent=2));print(out)
