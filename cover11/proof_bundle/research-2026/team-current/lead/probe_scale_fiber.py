"""Explicit-fiber separation control; exposes narrow-angle branches missed by constrainedDE."""
from pathlib import Path
import json,math
P=Path(__file__).parent;s=(P/'exchange_middle_inward_dual.py').read_text();marker='\n# Finite LP planes';assert s.count(marker)==1
ns={'__file__':str(P/'exchange_middle_inward_dual.py')};exec(s.split(marker)[0],ns)
np=ns['np'];DE=ns['differential_evolution'];value=ns['value'];R=.38;t0=75/76;pi=math.pi

def fiber_x(y):
 a,d,t=y;E=math.exp(2*abs(d));K=R*math.sqrt(2*(math.cosh(2*d)-math.cos(a)))/2;B=math.cos(a)+2*K*K*t0*t0
 if B>1:return None
 theta=math.acos(max(-1,B));lo=max((a-theta)/2,pi-8*math.asin(R));hi=min((a+theta)/2,math.asin(min(1,K*math.exp(-abs(d)))))
 if a<pi:hi=min(hi,math.atan2(math.sin(a),E+math.cos(a)))
 elif d!=0:return None
 if lo>hi:return None
 om=lo+t*(hi-lo);s=math.sin(om)/K
 return [a,s*math.exp(d),s*math.exp(-d)]

def fiber_oracle(fi,z,seed=0):
 def f(y):
  x=fiber_x(y)
  return 100 if x is None else -value(fi,x,z)
 sols=[]
 for al,ah,dl,dh in [(.0233,.15,-.16,.16),(.15,.7,-.5,.5),(.7,pi,-math.log(100/19)/2,math.log(100/19)/2)]:
  ss=DE(f,[(al,ah),(dl,dh),(0,1)],seed=2910+fi+seed,popsize=18,maxiter=220,tol=1e-10,polish=True)
  if fiber_x(ss.x) is not None:sols.append(ss)
 sol=min(sols,key=lambda x:x.fun)
 x=fiber_x(sol.x);assert x is not None
 return np.array(x),float(value(fi,x,z))
if __name__=='__main__':
 z=np.array(json.loads((P/'middle_inward_frozen.json').read_text())['z']);rows=[]
 for fi in [20,21,23,24,25,26,27,28]:
  x,v=fiber_oracle(fi,z);r={'factor':fi,'value':v,'x':x.tolist(),'margin':ns['margin'](x).tolist()};rows.append(r);print(r,flush=True)
 (P/'scale_fiber_oracle_control.json').write_text(json.dumps(rows,indent=2))
