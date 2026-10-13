"""Conditional sector2+neighbors+switches pointwise cluster diagnostic. NOT uppercertificate."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
from pathlib import Path
import math,json
import numpy as np
from scipy.optimize import differential_evolution,minimize,NonlinearConstraint
P=Path(__file__).parent;s=(P/'exchange_middle_inward_dual.py').read_text();marker='\n# Finite LP planes';assert s.count(marker)==1
ns={'__file__':str(P/'exchange_middle_inward_dual.py')};exec(s.split(marker)[0],ns);value=ns['value'];margin=ns['margin'];R=.38;pi=math.pi;tau=75/76
hist=json.loads((P/'middle_inward_fiber_exchange_history.json').read_text());row=min(hist,key=lambda r:r['continuous_numeric']);z=np.array(row['z']);inds=[21,22,23,12,13]
def sector(a,u,v):
 q=(u-v)**2+4*u*v*math.sin(a/2)**2;w=2*math.asin(R*math.sqrt(q)/2);L=math.atan2(v*math.sin(a),u-v*math.cos(a));return w,L,pi-a-L

def decode(x):
 t,a,u,c,v=x;w1,L1,T1=sector(a,u,t);w3,L3,T3=sector(c,t,v);w2=2*math.asin(R*t);b1=(pi-T1-(w1+w2)/2)/2;b2=(pi-L3-(w2+w3)/2)/2
 return [[a,u,t],[pi,t,t],[c,t,v],[b1,t],[b2,t]]
def constraints(x):
 pp=decode(x);b1,b2=pp[3][0],pp[4][0];t=x[0]
 return np.r_[margin(pp[0]),margin(pp[2]),b1,b2,pi/2-b1,pi/2-b2,2*t*math.cos(b1)-R*(t*t+max(tau*tau,t*t)),2*t*math.cos(b2)-R*(t*t+max(tau*tau,t*t))]
def fun(x):return -sum(value(fi,xx,z) for fi,xx in zip(inds,decode(x)))
bounds=[(tau,1),(.0233,pi),(.19,1),(.0233,pi),(.19,1)];rows=[]
for seed in range(3):
 sol=differential_evolution(fun,bounds,constraints=NonlinearConstraint(constraints,0,np.inf),seed=1100+seed,popsize=14,maxiter=160,polish=False)
 ss=minimize(fun,sol.x,method='SLSQP',bounds=bounds,constraints={'type':'ineq','fun':constraints},options={'maxiter':300,'ftol':1e-11})
 for tag,r in [('DE',sol),('SLSQP',ss)]:
  if min(constraints(r.x))>=-1e-8:rows.append({'seed':seed,'method':tag,'value':float(-fun(r.x)),'x':r.x.tolist(),'minmargin':float(min(constraints(r.x))),'atoms':decode(r.x)})
 print(seed,rows[-1] if rows else None,flush=True)
assert rows;best=max(rows,key=lambda r:r['value']);old=sum(row['factor_values'][i] for i in inds);total=row['continuous_numeric']-old+best['value'];result={'scope':'boundednumeric5factorcluster, no rigorousupper','source_round':row['round'],'source_total_numeric':row['continuous_numeric'],'independent_five_numeric':old,'cluster_numeric':best['value'],'diagnostic_total':total,'runs':rows};(P/'five_factor_cluster_probe.json').write_text(json.dumps(result,indent=2));print('TOTAL',total,flush=True)
