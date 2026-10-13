"""Can independent norm-circle side maxima already exclude both-low? numeric diagnostic."""
import math,json,numpy as np
from scipy.optimize import minimize
from probe_lowbearing_stationary import z,R,P
r=.37999;s=math.sqrt(1-r*r)
K=math.pi*(z[113]+z[114]-z[2])+math.pi/2*(z[112]+z[115]-z[1]-z[3])+(1-z[1]-z[3])*math.asin(r)
def fun(q,j):
 b,p=q;v=s+(1-r)*math.cos(p);t=(1-r)*math.sin(p);x0=2*b-math.acos(r);X=r*math.sin(x0);D=1-r*math.cos(x0);w=2*math.atan2(X,D);mu,h,d,l=(z[1],z[112],z[34],z[96])if j==0 else(z[3],z[115],z[39],z[101]);a,bb,gg,sg=(z[1]-z[9],-z[16],-z[78],-1)if j==0 else(z[3]-z[9],z[20],z[82],1)
 ex=v-r*math.sin(2*b);ey=2*r*math.sin(b)**2+sg*t;e=math.hypot(ex,ey)/(2*R)
 return -r*s*math.sin(b)**2+(.5-mu)*w-X/2-(mu+h)*x0-d*(r/R)**2-l*r/R+r*math.sin(b)**2*v+sg*r*math.sin(b)*math.cos(b)*t+a*math.atan2(ey,ex)+bb*e*e+gg*e

def cons(q,j):
 b,p=q;sg=-1 if j==0 else 1;v=s+(1-r)*math.cos(p);t=(1-r)*math.sin(p);x0=2*b-math.acos(r);w=2*math.atan2(r*math.sin(x0),1-r*math.cos(x0))
 return [r*r-(v-r*math.sin(2*b))**2-(t-sg*r*math.cos(2*b))**2,v*math.tan(b)+sg*t,w-.04644456359141745]
rows=[]
for j in [0,1]:
 ss=[]
 for b,p in [(.8,2.5),(.8,3.7),(.95,math.pi),(.7,2.8)]:
  sol=minimize(lambda q:-fun(q,j),[b,p],method='SLSQP',bounds=[(math.acos(r)/2,1),(1.8,4.5)],constraints=[{'type':'ineq','fun':lambda q:cons(q,j)}],options={'ftol':1e-12,'maxiter':150})
  if min(cons(sol.x,j))>-1e-7:ss.append({'j':j,'value':fun(sol.x,j),'point':sol.x.tolist(),'slack':cons(sol.x,j)})
 rows.append(max(ss,key=lambda a:a['value']))
out={'rows':rows,'sum':K+sum(a['value']for a in rows),'scope':'numeric independent side maxima at one radius; no certificate'};(P/'norm_separated_probe.json').write_text(json.dumps(out,indent=2));print(out)
