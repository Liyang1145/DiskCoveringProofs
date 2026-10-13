"""Bounded NUMERIC mechanism test for positive endpoint lowerbound; not intervalcertificate."""
import json,math,numpy as np
from scipy.optimize import minimize_scalar
from fractions import Fraction as Q
from joint_innernorm_probe import P,r,lines,fval
D=json.loads((P/'joint-innernorm-probe.json').read_text());saved=[json.loads(x)for x in(P/'joint-innernorm-catalogue.jsonl').read_text().splitlines()];rows=[]
for fam in ['10/4','11/3']:
 rows+=sorted([x for x in saved if x['family']==fam and x['status']=='inconclusive'],key=lambda x:x['upper_display'])[:6]
out=[]
for row in rows:
 q=int(row['family'].split('/')[0]);nu=float(Q(row['rational_nu']));lam=float(Q(row['rational_lambda']));y=list(map(float,map(Q,row['rational_potentials'])));delta=1-math.cos(math.pi/q);A=2*math.asin(r/2);c=(A-math.sin(A))/2+nu*A;diff=0;active=0;oldtotal=0;newtotal=0
 def h(t):return min(float(a)+float(k)*t for a,k in lines)
 def sup(fn):
  xx=np.linspace(0,math.pi,65);vals=[fn(x)for x in xx]
  for j in range(len(xx)-1):
   z=minimize_scalar(lambda t:-fn(t),bounds=(xx[j],xx[j+1]),method='bounded');vals.append(-z.fun)
  return max(vals)
 for j in range(q):
  rr=sup(lambda t:fval(t,nu)+lam*h(t)-y[j]*t);old=sup(lambda t:c+lam*h(t)-y[j]*t)
  def cross(t):
   d=math.sqrt(r*r+delta*delta-2*r*delta*math.cos(t));th=2*math.asin(d/2);return r*delta/2*math.sin(t)+(th-math.sin(th))/2+nu*th+lam*h(t)-y[j]*t
  new=sup(cross);oldtotal+=max(rr,old);newtotal+=max(rr,new);active+=int(old>rr)
 out.append({'family':row['family'],'index':row['index'],'old_bound':row['upper_display'],'numeric_delta':delta,'old_cross_active':active,'numeric_bound_delta':newtotal-oldtotal,'numeric_new_bound_estimate':row['upper_display']+newtotal-oldtotal});print(out[-1],flush=True)
(P/'lower-endpoint-probe.json').write_text(json.dumps({'status':'numeric_only_not_certificate','scope':'12closestcurrentlyavailablejointsurvivors','runs':out},indent=2))
