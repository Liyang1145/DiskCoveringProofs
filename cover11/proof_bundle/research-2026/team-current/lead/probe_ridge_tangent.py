"""Bounded numerical diagnostic for exact concave rank-one ridge split; no certificate."""
import numpy as np,math,json
from scipy.optimize import differential_evolution
from pathlib import Path
P=Path(__file__).parent;z=np.array(json.loads((P/'joint_nested_frozen.json').read_text())['z']);R=.38;g=2*math.pi-16*math.asin(R)
def part(r,b,w,j,tau):
 s=math.sqrt(1-r*r);ph=math.asin(r);x0=2*b-math.pi/2+ph;p=math.cos(w)-r*math.cos(x0+w);x=-math.sin(w)+r*math.sin(x0+w);q=r*r+4*math.sin(w/2)**2-4*r*math.sin(x0+w/2)*math.sin(w/2)
 if q<=0 or 1-p<=0 or q>r*r+1e-13:return -1e9
 mu,h,d,l=(z[1],z[112],z[34],z[96])if j==0 else(z[3],z[115],z[39],z[101])
 val=-r*s*math.sin(b)**2+(.5-mu)*w+x/2+(mu+h)*math.atan2(x,1-p)-d*q/R**2-l*math.sqrt(q)/R
 bb,gg,aa=(z[20],z[82],z[3]-z[9])if j==0 else(-z[16],-z[78],z[1]-z[9])
 e=r*math.sin(b)/R
 return val+r*r*math.sin(2*b)+aa*b+bb*e*e+gg*e-2*r*r*math.cos(2*tau)*b
out=[]
for r in [.37999]:
 for tau in [2.1,2.175,2.25]:
  rows=[]
  for j in [0,1]:
   ans=differential_evolution(lambda y:-part(r,*y,j,tau),[(1,math.acos(r)),(g,2*math.asin(r))],seed=170+j,popsize=10,maxiter=80,tol=1e-10,polish=True)
   rows.append({'j':j,'value':-ans.fun,'b_w':ans.x.tolist()})
  K=math.pi*(z[113]+z[114]-z[2])+math.pi/2*(z[112]+z[115]-z[1]-z[3])+(1-z[1]-z[3])*math.asin(r)
  total=K+r*r*(-math.sin(2*tau)+2*tau*math.cos(2*tau))+sum(t['value'] for t in rows)
  out.append({'r':r,'tau':tau,'numeric_tangent_sup':total,'components':rows})
(P/'ridge_tangent_probe.json').write_text(json.dumps(out,indent=2));print(out)
