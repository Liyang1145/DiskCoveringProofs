"""Independent boundaryfirst 4Douter+3scalarfiber numerical attack. No uppercertificate."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
from pathlib import Path
import math,json,numpy as np
from scipy.optimize import differential_evolution,minimize_scalar
P=Path(__file__).parent;s=(P/'check_arc_chart.py').read_text();m="\nif __name__";assert s.count(m)==1
ns={'__file__':str(P/'check_arc_chart.py')};exec(s.split(m)[0],ns);R=.38;pi=math.pi;z=np.array(json.loads((P/'joint_nested_frozen.json').read_text())['z']);ns['reduced'].__globals__['z']=z;g=ns['g'];width=ns['width'];sectorleft=ns['sectorleft']
def scalarmax(fun,lo,hi):
 grid=np.linspace(lo,hi,13);vals=[fun(x) for x in grid];choices=list(zip(vals,grid))
 for j in range(1,12):
  if vals[j]>=max(vals[j-1],vals[j+1]):
   ss=minimize_scalar(lambda x:-fun(x),bounds=(grid[j-1],grid[j+1]),method='bounded',options={'xatol':1e-10});choices.append((-ss.fun,ss.x))
 return max(choices)
def evaluate(y,detail=False):
 r,q1,q2,qA=y;bc=math.acos(r);b1=bc*(.5+.5*q1);b2=bc*(.5+.5*q2);A=qA*(b1+b2);B=b1+b2-A;delta=b1-A;s=math.sqrt(1-r*r);disc=s*s*math.cos(delta)**2-2*r*(1-r)
 if disc<0:return None
 lo=max(2*r*abs(math.sin(delta)),s*math.cos(delta)-math.sqrt(disc));hi=min(2*r*math.sin(b1+A),2*r*math.sin(b2+B),s*math.cos(delta)+math.sqrt(disc));W1,W3=width(r,b1),width(r,b2)
 if lo>hi or min(W1,W3)<g:return None
 D1,D2=2*r*math.sin(b1),2*r*math.sin(b2)
 def hf(H):
  h1=math.atan2(D1*math.sin(A),H-D1*math.cos(A));h2=math.atan2(D2*math.sin(B),H-D2*math.cos(B));e1=math.hypot(H-D1*math.cos(A),D1*math.sin(A))/(2*R);e3=math.hypot(H-D2*math.cos(B),D2*math.sin(B))/(2*R)
  return H*(D1*math.sin(A)+D2*math.sin(B))/2+(z[1]-z[9])*h1+(z[3]-z[9])*h2-z[16]*e1*e1-z[78]*e1+z[20]*e3*e3+z[82]*e3
 def wf(w,b,i):
  a,u=sectorleft(r,b,w);t=r/R;L=math.atan2(t*math.sin(a),u-t*math.cos(a));mu,h,d,dl=(z[1],z[112],z[34],z[96])if i==1 else (z[3],z[115],z[39],z[101])
  return R*r*u*math.sin(a)/2+(w-math.sin(w))/2-mu*a-d*u*u-dl*u+h*(L+w/2)
 hm,H=scalarmax(hf,lo,hi);fm,w1=scalarmax(lambda w:wf(w,b1,1),g,W1);gm,w3=scalarmax(lambda w:wf(w,b2,3),g,W3)
 w2=2*math.asin(r);K=pi*(z[113]+z[114]-z[2])+z[1]*(b1-pi+A)+z[3]*(b2-pi+B)+(w2-math.sin(w2))/2+r*r*(math.sin(2*b1)+math.sin(2*b2))/2
 total=K+hm+fm+gm
 if not detail:return total
 y7=[r,b1,b2,(w1-g)/(W1-g),(w3-g)/(W3-g),qA,(H-lo)/(hi-lo)];x=ns['chart'](y7);direct=ns['reduced'](x);assert abs(direct-total)<1e-8
 return {'value':total,'outer':list(y),'widths':[w1,w3],'H':H,'chart':y7,'originalx':x.tolist(),'directvalue':direct}
if __name__=='__main__':
 rows=[]
 for seed in range(6):
  def f(y):
   v=evaluate(y);return 1e3 if v is None else -v
  sol=differential_evolution(f,[(.375,.38),(0,1),(0,1),(.0001,.9999)],seed=1300+seed,popsize=14,maxiter=140,tol=1e-9,polish=True);rr=evaluate(sol.x,True);rows.append(rr);print(rr,flush=True)
 (P/'nested_patch_frozen_attack.json').write_text(json.dumps({'scope':'4Dnestednumeric attack, not uppercertificate','runs':rows},indent=2))
