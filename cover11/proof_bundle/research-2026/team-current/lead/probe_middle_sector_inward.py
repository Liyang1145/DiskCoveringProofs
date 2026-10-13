"""One bounded analytic-interface diagnostic: inward-norm constrained sector maxima.
Existingfrozen dual, 9ring factors,3fixed starts+DEproposal each; numeric ONLY.
"""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
from pathlib import Path
import numpy as np,math,json
from scipy.optimize import differential_evolution,minimize,NonlinearConstraint
P=Path(__file__).parent;z=np.array(json.loads((P/'middle_sector_inward_dual_proposal.json').read_text())['z']);R=.38;pi=math.pi;tmin=75/76;qmin=4*math.sin(pi-8*math.asin(R))**2/R**2
def geom(x):
 a,u,v=x;Q=(u-v)**2+4*u*v*math.sin(a/2)**2;h=R*math.sqrt(max(Q,0))/2;k=math.sqrt(1-h*h);return Q,h,k
def margin(x):
 a,u,v=x;Q,h,k=geom(x);return np.r_[Q-qmin,u*v*(k*math.sin(a)-h*math.cos(a))-max(tmin*tmin,u*u,v*v)*h]
def val(i,x):
 a,u,v=x;Q,h,k=geom(x);w=2*math.asin(h);L=math.atan2(v*math.sin(a),u-v*math.cos(a));T=pi-a-L
 return R*R*u*v*math.sin(a)/2+(w-math.sin(w))/2-z[i]*a-z[32+2*i]*u*u-z[33+2*i]*v*v-z[94+2*i]*u-z[95+2*i]*v+z[71]*w+z[112+(i-1)%9]*(L+w/2)+z[112+i]*(T+w/2)
rows=[]
for i in range(9):
 de=differential_evolution(lambda x:-val(i,x),[(.02,pi),(1e-5,1),(1e-5,1)],constraints=NonlinearConstraint(margin,0,np.inf),seed=847+i,popsize=12,maxiter=120,polish=False)
 best=None
 for x in [de.x,[1.,1.,1.],[pi-1e-5,.999,.999]]:
  s=minimize(lambda x:-val(i,x),x,method='SLSQP',bounds=[(.02,pi),(1e-5,1),(1e-5,1)],constraints={'type':'ineq','fun':margin},options={'maxiter':150,'ftol':1e-11})
  if min(margin(s.x))>=-1e-9 and (best is None or -s.fun>best['value']):best={'value':float(-s.fun),'x':s.x.tolist(),'minmargin':float(min(margin(s.x))),'success':bool(s.success)}
 assert best is not None;best['sector']=i;rows.append(best);print(i,best,flush=True)
num_total=None # otherfactorbounds still need fresh evaluation; neverreuse differentdualbounds
out={'scope':'finite constrainedoptimizationdiagnostic, NOT rigorousupper; decision whether inwardnorm filter materiallytightens fixeddual','rows':rows,'numeric_total':num_total}
(P/'middle_sector_inward_continuum_probe.json').write_text(json.dumps(out,indent=2));print('NUMERIC_TOTAL',num_total,flush=True)
