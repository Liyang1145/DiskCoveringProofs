"""Exactdecimal intervalcounterexample to globalridgeobjective maximization, notcover."""
from pathlib import Path
import json
import interval_joint_patch as k
from interval_joint_patch import I,iv,R,z,pi,asin,acos
from cartesian_hub_jet import objective
P=Path(__file__).parent
lit=['0.3750951887748506','0.9471039318692589','0.9148561742031202','0.4089871357815944','-0.2502035007058863']
r,b1,b2,v,t=map(I,lit);s=iv.sqrt(1-r*r);T=b1+b2;D=b1-b2
points={'witness':(v,t),'ridge':(2*r*iv.sin(T)*iv.cos(D),2*r*iv.sin(T)*iv.sin(D))};res={}
for name,(v,t)in points.items():
 margins=[r*r-(v-r*iv.sin(2*b1))**2-(t+r*iv.cos(2*b1))**2,r*r-(v-r*iv.sin(2*b2))**2-(t-r*iv.cos(2*b2))**2,(1-r)**2-(v-s)**2-t*t,v,t+v*iv.tan(b2),v*iv.tan(b1)-t]
 if name=='witness':assert all(m.a>0 for m in margins)
 # Ridge faceequalities analyticC855; intervalsaroundzero not usedasequalityproof.
 val=objective([r,b1,b2,v,t]).v
 H=iv.sqrt(v*v+t*t);de=iv.atan2(t,v);old=(z[3]-z[1])*de
 for b,th,a,bb,gg in [(b1,b1-de,z[1]-z[9],-z[16],-z[78]),(b2,b2+de,z[3]-z[9],z[20],z[82])]:
  dd=2*r*iv.sin(b);Y=dd*iv.sin(th);X=H-dd*iv.cos(th);ell=iv.sqrt(X*X+Y*Y)/(2*R);old+=H*Y/2+a*iv.atan2(Y,X)+bb*ell*ell+gg*ell
 diff=val-old;assert diff.a<=0<=diff.b
 res[name]={'margins':[str(m)for m in margins],'cartesian':str(val),'polar':str(old),'value':val}
for b in [b1,b2]:
 bc=acos(r);bmin=(bc+asin(iv.sin(k.g/2)/r)-k.g/2)/2
 assert b.a>bmin.b and b.b<bc.a
# Samelegalwidths g for bothpoints, so allnonhubtermscancel.
gain=res['witness']['value']-res['ridge']['value'];assert gain.a>I('.04615').b
for q in res.values():del q['value']
out={'scope':'C848localnecessaryfamily; counterexample to globalridgeonly, notcovercounterexample','exact_decimal_input':lit,'comparisons':res,'witness_minus_ridge':str(gain),'width_choice':'w1=w3=g=2pi-16asin(19/50)'};(P/'nonridge_witness_certificate.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
