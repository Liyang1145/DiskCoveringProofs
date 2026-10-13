import interval_joint_patch as k
from pathlib import Path
import json
r=k.I('.379','.38');b1=k.I('1.106','1.108');b2=k.I('1.068','1.071');de=b1-b2;H=2*r*k.iv.sin(b1+b2);s=k.iv.sqrt(1-r*r)
sep=H-2*r*abs(k.iv.sin(de));norm=H*H-2*s*k.iv.cos(de)*H+2*r*(1-r)
assert sep.a>0 and norm.b<0
out={'r':['.379','.38'],'b1':['1.106','1.108'],'b2':['1.068','1.071'],'delta_ridge':[k.lf(de),k.uf(de)],'Hlower_margin':[k.lf(sep),k.uf(sep)],'hubnorm_residual':[k.lf(norm),k.uf(norm)],'scope':'ridgefeasiblethroughout3Dbox; faceupperconstraintsbothsaturatedexactly'};Path(__file__).with_name('delta_ridge_feasibility.json').write_text(json.dumps(out,indent=2));print(out)
