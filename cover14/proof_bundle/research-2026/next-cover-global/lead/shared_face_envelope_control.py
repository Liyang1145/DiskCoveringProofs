"""Calibrate exact local face envelope against actual geometry; numeric only."""
from boundary_radius_control import *
rows=[]
for j,f in enumerate(faces):
 ee=[tuple(sorted(e))for e in combinations(f,2)];bs=[beta[e]for e in ee];ss=sum(bs);a=sum(math.sin(b)for b in bs);b=sum(math.sin(u+v)for u,v in combinations(bs,2));c=math.sin(ss)
 if ss<=math.pi+1e-14:x0=1.
 else:x0=(b+math.sqrt(b*b-4*a*c))/(2*a)
 actual=sum(U*U*math.sin(beta[e])-loss[e]for e in ee);cap=U*U*x0*a;assert actual<=cap+2e-14
 if ss>math.pi+1e-14:assert abs(sum(math.atan2(math.sin(v),x0-math.cos(v))for v in bs)-math.pi)<1e-12
 rows.append({'face':j,'sum_beta':ss,'x0':x0,'actual':float(actual),'cap':cap,'slack':float(cap-actual)})
(P/'shared-face-envelope-control.json').write_text(json.dumps({'status':'numeric_control_only','faces':rows},indent=2));print('faces',len(rows),'slackfaces',rows[14:])
