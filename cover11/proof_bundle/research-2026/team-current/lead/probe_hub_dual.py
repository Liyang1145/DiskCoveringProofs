"""Bounded numeric test of ridge diskdual concavity mechanism, not certificate."""
import math,json,numpy as np
from pathlib import Path
P=Path(__file__).parent;z=json.loads((P/'joint_nested_frozen.json').read_text())['z'];R=.38

def dual(r,b1,b2):
 T=b1+b2;D=b1-b2;v=2*r*math.sin(T)*math.cos(D);t=2*r*math.sin(T)*math.sin(D)
 grad=np.array([r*(math.sin(b1)**2+math.sin(b2)**2),r*(math.sin(b2)*math.cos(b2)-math.sin(b1)*math.cos(b1))]);hess=np.zeros((2,2));minL=[];beta=[];a=[];gam=[]
 for b,sg,aa,bb,gg in [(b1,-1,z[1]-z[9],-z[16],-z[78]),(b2,1,z[3]-z[9],z[20],z[82])]:
  X=v-r*math.sin(2*b);Y=2*r*math.sin(b)**2+sg*t;L=math.hypot(X,Y);bb/=4*R*R;gg/=2*R
  grad+=np.array([-aa*Y/L**2+(2*bb+gg/L)*X,sg*(aa*X/L**2+(2*bb+gg/L)*Y)])
  s=math.sqrt(1-r*r);cn=1+r*r-2*r*math.cos(2*b-math.acos(r));minL.append(math.sqrt(cn)-(1-r));beta.append(bb);a.append(aa);gam.append(gg)
 centers=[np.array([r*math.sin(2*b1),-r*math.cos(2*b1)]),np.array([r*math.sin(2*b2),r*math.cos(2*b2)])];point=np.array([v,t]);norms=np.array([2*(point-c)for c in centers]).T
 if abs(np.linalg.det(norms))<1e-9:return None
 lam=np.linalg.solve(norms,grad)
 # bound maxeigen Hess(sumradial+angle)<=sum(2beta+a²/(|gamma|L³))
 cap=sum(2*b+a0*a0/(abs(g)*l**3)for b,a0,g,l in zip(beta,a,gam,minL))
 return {'outer':[r,b1,b2],'lambda':lam.tolist(),'minL':minL,'hessian_cap':cap,'penalty_curvature':2*sum(lam),'gap':2*sum(lam)-cap}
rows=[dual(.38,b1,b2)for b1 in np.linspace(.9,1.18,8)for b2 in np.linspace(.9,1.18,8)];rows=[r for r in rows if r];out={'scope':'numericmechanismtest','positive_lambdas':sum(min(r['lambda'])>=0 for r in rows),'concavity_sufficient':sum(min(r['lambda'])>=0 and r['gap']>=0 for r in rows),'count':len(rows),'worst':min(rows,key=lambda r:r['gap']),'best':max(rows,key=lambda r:r['gap']),'local':dual(.38,1.107,1.0695)};(P/'hub_dual_probe.json').write_text(json.dumps(out,indent=2,default=float));print(json.dumps(out,indent=2,default=float))
