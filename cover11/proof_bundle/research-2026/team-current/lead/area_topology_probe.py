import math,json
from scipy.optimize import minimize
r=.38
pi=math.pi
amin=2*math.asin(math.sin(pi/9)/r)
def F(a):
 b=2*math.asin(r*math.sin(a/2))
 return r*r*math.sin(a)/2+(b-math.sin(b))/2
def val(a,t,K,d):
 bh=K-2*d;rr=21-K+d
 x=(4*pi-2*d*t)/bh;y=(7*pi-4.5*a+d*t)/rr
 return r*r*(bh*math.sin(x)+rr*math.sin(y)+d*math.sin(t))+9*F(a)
rows=[]
for d in [0,1]:
 for K in range(6,13+d):
  bh=K-2*d;rr=21-K+d
  def c(x):
   a,t=x;return [4*pi-2*d*t,bh*pi-4*pi+2*d*t,7*pi-4.5*a+d*t,rr*pi-7*pi+4.5*a-d*t]
  res=minimize(lambda x:-val(x[0],x[1],K,d),[(amin+pi)/2,pi/2],bounds=[(amin,pi),(0,pi)],constraints=[{'type':'ineq','fun':c}],method='SLSQP',options={'ftol':1e-13,'maxiter':500})
  rows.append(dict(d=d,K=K,area=-float(res.fun),deficit=pi+float(res.fun),a=float(res.x[0]),t=float(res.x[1]),success=bool(res.success)))
print(json.dumps({'r':r,'amin':amin,'rows':rows},indent=2))
