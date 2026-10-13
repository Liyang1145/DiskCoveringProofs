"""Attack best jointfactor proposal using distinct angle strata, full retainedplanes."""
from pathlib import Path
import numpy as np,json,math
P=Path(__file__).parent;s=(P/'exchange_joint_patch.py').read_text();mark='\nrows=[]';assert s.count(mark)==1
ns={'__file__':str(P/'exchange_joint_patch.py')};exec(s.split(mark)[0],ns)
from scipy.optimize import differential_evolution,minimize,NonlinearConstraint
hist=json.loads((P/'joint_patch_exchange_refined.json').read_text());best=min(hist,key=lambda r:r['numeric_total']);z=np.array(best['z']);catom=ns['catom'];margins=ns['margins'];bounds=ns['bounds'];runs=[]
def fun(x):
 a=catom(x)
 return 1000 if a is None else -(a[0]+a[1]@z)
for k,(aa,bb) in enumerate([(a,b)for a in [(.0233,.15),(.15,.7),(.7,math.pi)] for b in [(.0233,.15),(.15,.7),(.7,math.pi)]]):
 dom=bounds.copy();dom[1]=aa;dom[3]=bb
 sol=differential_evolution(fun,dom,constraints=NonlinearConstraint(margins,0,np.inf),seed=1230+k,popsize=18,maxiter=250,polish=False)
 ss=minimize(fun,sol.x,bounds=dom,method='SLSQP',constraints={'type':'ineq','fun':margins},options={'maxiter':300,'ftol':1e-11})
 for name,r in [('DE',sol),('SLSQP',ss)]:
  if catom(r.x) is not None and min(margins(r.x))>=-1e-8:runs.append({'branch':k,'method':name,'value':float(-fun(r.x)),'x':r.x.tolist(),'margin':float(min(margins(r.x)))})
 print('BRANCH',k,'best',max((r['value']for r in runs if r['branch']==k),default=None),flush=True)
result={'source_round':best['round'],'source_total':best['numeric_total'],'source_cluster':best['factor_values'][-1],'runs':runs,'attack_cluster':max(r['value']for r in runs)};result['new_numeric_total']=best['numeric_total']-best['factor_values'][-1]+result['attack_cluster'];(P/'joint_patch_attack.json').write_text(json.dumps(result,indent=2));print('SUMMARY',{k:v for k,v in result.items()if k!='runs'},flush=True)
