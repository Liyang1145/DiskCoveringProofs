"""Exact rational controls for weak quadratic dual; not a global sharp certificate."""
from fractions import Fraction as F
from pathlib import Path
import json

def lower(p,r,alpha,q,s,beta):
 p=[[F(v) for v in a] for a in p];q=[[F(v) for v in a] for a in q]
 r=list(map(F,r));s=list(map(F,s));alpha=list(map(F,alpha));beta=list(map(F,beta))
 A=sum(alpha);B=sum(beta);delta=A+B+A*B;assert delta>0
 P=[sum(w*a[k] for w,a in zip(alpha,p)) for k in range(2)]
 Q=[sum(w*a[k] for w,a in zip(beta,q)) for k in range(2)]
 dot=lambda a,b:sum(x*y for x,y in zip(a,b))
 T=sum(w*(dot(a,a)-v*v) for w,a,v in zip(alpha,p,r))+sum(w*(dot(a,a)-v*v) for w,a,v in zip(beta,q,s))
 return T-((1+B)*dot(P,P)+2*dot(P,Q)+(1+A)*dot(Q,Q))/delta
x=lower([[0,0]],[1],[1],[[3,0]],[1],[1]);assert x==1
y=lower([[0,0]],[1],[1],[[0,0]],[1],[1]);assert y==-2
vals=[]
for t in [1,2,10,100]:
 z=lower([[-1,0],[1,0]],[1,1],[t,t],[[0,3]],[1],[2]);assert z==4-F(6,1+3*t) and z<4;vals.append([t,str(z)])
out={'scope':'exact rational calibration of universal weak dual only','separated_unit_disks':str(x),'coincident_disks':str(y),'singleton_CQ_failure':vals,'singleton_limit':'4 from below; normals only span x-axis'}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2));print(out)
