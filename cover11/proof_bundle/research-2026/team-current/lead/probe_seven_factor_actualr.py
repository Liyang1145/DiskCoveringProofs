"""Conditional sevenfactor hubpatch diagnostic. Finite optimizer, not proof."""
from pathlib import Path
import math,json,numpy as np
from scipy.optimize import differential_evolution,minimize,NonlinearConstraint
P=Path(__file__).parent;s=(P/'probe_five_factor_cluster.py').read_text();marker='\nbounds=';assert s.count(marker)==1
ns={'__file__':str(P/'probe_five_factor_cluster.py')};exec(s.split(marker)[0],ns)
base_decode=ns['decode'];old_constraints=ns['constraints'];value=ns['value'];z=ns['z'];row=ns['row'];R=.38;pi=math.pi;tau=75/76

def base_constraints(x):
 pp=base_decode(x);t=x[0];extra=[]
 for a,u,v in [pp[0],pp[2]]:
  q=(u-v)**2+4*u*v*math.sin(a/2)**2;h=R*math.sqrt(q)/2;k=math.sqrt(1-h*h)
  extra.extend([t-u,t-v,u*v*(k*math.sin(a)-h*math.cos(a))-t*t*h])
 return np.r_[old_constraints(x),extra]
def patch(x):
 base=base_decode(x[:5]);b1,b2=base[3][0],base[4][0];t=x[0];r=R*t;A=x[5]*(b1+b2);B=b1+b2-A;delta=b1-A;s=math.sqrt(1-r*r)
 if min(A,B,b1,b2)<=0 or max(A,B)>=pi:return None
 dd=s*s*math.cos(delta)**2-2*r*(1-r)
 if dd<0:return None
 root=math.sqrt(dd);lo=max(2*r*abs(math.sin(delta)),s*math.cos(delta)-root);hi=min(2*r*math.sin(b1+A),2*r*math.sin(b2+B),s*math.cos(delta)+root)
 if lo>hi or hi<=0:return None
 H=lo+x[6]*(hi-lo);args=[]
 for j,(a,b) in enumerate([(A,b1),(B,b2)]):
  D=2*r*math.sin(b);hub=math.atan2(D*math.sin(a),H-D*math.cos(a));other=pi-a-hub;rho=math.sqrt(max(0,H*H+D*D-2*H*D*math.cos(a)))/(2*math.sin(a))
  if other<=0:return None
  args.append([hub,other if j==0 else a,rho/R])
 return base,args,{'H':H,'A':A,'B':B,'Hlo':lo,'Hhi':hi,'r':r}

def margins(x):
 pp=patch(x)
 if pp is None:return np.r_[base_constraints(x[:5]),-1.]
 return np.r_[base_constraints(x[:5]),1.]
def fun(x):
 pp=patch(x)
 if pp is None:return 1000
 base,args,_=pp
 return -(sum(value(fi,xx,z) for fi,xx in zip([21,22,23,12,13],base))+sum(value(fi,xx,z)for fi,xx in zip([1,2],args)))
bounds=[(tau,1),(.0233,pi),(.19,1),(.0233,pi),(.19,1),(1e-5,1-1e-5),(0,1)];rows=[]
for seed in range(3):
 ss=differential_evolution(fun,bounds,constraints=NonlinearConstraint(margins,0,np.inf),seed=1120+seed,popsize=16,maxiter=200,polish=False)
 tt=minimize(fun,ss.x,method='SLSQP',bounds=bounds,constraints={'type':'ineq','fun':margins},options={'maxiter':350,'ftol':1e-10})
 for name,r in [('DE',ss),('SLSQP',tt)]:
  if patch(r.x) is not None and min(margins(r.x))>=-1e-8:rows.append({'seed':seed,'method':name,'value':float(-fun(r.x)),'x':r.x.tolist(),'minmargin':float(min(margins(r.x))),'patch':patch(r.x)})
 print(seed,rows[-1] if rows else None,flush=True)
assert rows;best=max(rows,key=lambda r:r['value']);old=sum(row['factor_values'][i]for i in [21,22,23,12,13,1,2]);total=row['continuous_numeric']-old+best['value']
(P/'seven_factor_actualr_probe.json').write_text(json.dumps({'scope':'numericalsevenfactorpatch, not uppercertificate','source_round':row['round'],'old_seven_numeric':old,'joint_numeric':best['value'],'diagnostic_total':total,'runs':rows},indent=2));print('TOTAL',total,flush=True)
