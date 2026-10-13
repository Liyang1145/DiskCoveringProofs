"""Fixed-r numeric boundary maximum diagnostics, not continuum bounds."""
import numpy as np,math,json
from scipy.optimize import minimize
from probe_lowbearing_stationary import z,R,residuals,P
r=.37999;s=math.sqrt(1-r*r);g=.04644456359141745
K=math.pi*(z[113]+z[114]-z[2])+math.pi/2*(z[112]+z[115]-z[1]-z[3])+(1-z[1]-z[3])*math.asin(r)
def endpoint(b,j):
 x0=2*b-math.acos(r);X=r*math.sin(x0);D=1-r*math.cos(x0);w=2*math.atan2(X,D);mu,h,d,l=(z[1],z[112],z[34],z[96])if j==0 else(z[3],z[115],z[39],z[101]);return -r*s*math.sin(b)**2+(.5-mu)*w-X/2-(mu+h)*x0-d*(r/R)**2-l*r/R,w

def geom(q,j):
 b1,b2,p=q
 if j<2:
  H=2*r*math.sin(2*b1-p)if j==0 else 2*r*math.sin(2*b2+p);return H*math.cos(p),H*math.sin(p)
 return s+(1-r)*math.cos(p),(1-r)*math.sin(p)
def objective(q,j):
 b1,b2,p=q;v,t=geom(q,j);ans=K+endpoint(b1,0)[0]+endpoint(b2,1)[0]+r*(math.sin(b1)**2+math.sin(b2)**2)*v+r*(math.sin(b2)*math.cos(b2)-math.sin(b1)*math.cos(b1))*t
 for b,sg,a,bb,gg in [(b1,-1,z[1]-z[9],-z[16],-z[78]),(b2,1,z[3]-z[9],z[20],z[82])]:
  X=v-r*math.sin(2*b);Y=2*r*math.sin(b)**2+sg*t;e=math.hypot(X,Y)/(2*R);ans+=a*math.atan2(Y,X)+bb*e*e+gg*e
 return ans
def constraints(q,j):
 b1,b2,p=q;v,t=geom(q,j);rr=residuals((v,t),r,b1,b2);rr.pop(j)
 return np.array([-a for a in rr]+[endpoint(b1,0)[1]-g,endpoint(b2,1)[1]-g])
rows=[]
for j in range(3):
 for start in [[.7,.8],[.9,.95],[1,.8],[1,1]]:
  q=start+[0 if j<2 else math.pi];sol=minimize(lambda q:-objective(q,j),q,method='SLSQP',bounds=[(math.acos(r)/2,1)]*2+[(-1,1)if j<2 else(2,4.3)],constraints=[{'type':'ineq','fun':lambda q:constraints(q,j)}],options={'maxiter':150,'ftol':1e-12})
  if min(constraints(sol.x,j))>-1e-7:rows.append({'j':j,'value':objective(sol.x,j),'x':sol.x.tolist(),'slack':constraints(sol.x,j).tolist(),'success':bool(sol.success)})
(P/'low_low_numeric_control.json').write_text(json.dumps(rows,indent=2));print(sorted(rows,key=lambda a:-a['value'])[:3])
