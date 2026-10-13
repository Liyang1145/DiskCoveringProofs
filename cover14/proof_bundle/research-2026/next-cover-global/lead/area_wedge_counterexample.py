"""Exact interval disproof of naive owned-subarc wedgebound; no covercounterexample."""
import json
from root_integer_certificate import I,Q,S
from pathlib import Path
P=Path(__file__).resolve().parent
r=I(Q(33173203427623414,10**17));s=(1-r*r).sqrt();c=(s,I(0));x=(s,-r);y=(((1+s)/2).sqrt(),-((1-s)/2).sqrt())
def dot(p,q):return sum((a*b for a,b in zip(p,q)),I(0))
u=[x[j]-c[j]for j in range(2)];v=[y[j]-c[j]for j in range(2)]
assert (r*r-dot(v,v)).lo>0
cosa=dot(u,v)/(dot(u,u)*dot(v,v)).sqrt();costheta=dot(x,y)
# theta<=2asin(r sin(alpha/2)) iff 1-cos(theta)<=r²(1-cos(alpha)), allanglesin[0,pi].
diff=1-costheta-r*r*(1-cosa);assert diff.lo>0
out={'status':'counterexample_to_naive_owned_subarc_wedge_inequality','scope':'singleinner-normalizedboundarydisk andsubarc, not14diskcoverorFejesTothpaperdisproof','radius':'33173203427623414/100000000000000000','center':'(sqrt(1-r²),0)','x':'(sqrt(1-r²),-r)','y':'(sqrt((1+sqrt(1-r²))/2),-sqrt((1-sqrt(1-r²))/2))','positive_violation_exact':diff.dec(),'positive_violation_display':diff.lo/S}
(P/'area-wedge-counterexample.json').write_text(json.dumps(out,indent=2));print(out['status'],out['positive_violation_display'])
