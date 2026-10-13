"""Diagnostic only: evaluate valid chord-envelope relaxation dual, no concavity premise."""
import numpy as np, math,json
from pathlib import Path
from scipy.optimize import minimize
R=.38;a=np.linspace(0,math.pi,4001)
w=2*np.arcsin(R*np.maximum(.5,np.sin(a/2)))
F=.5*R*R*np.sin(a)+.5*(w-np.sin(w))
J=json.loads(Path(__file__).with_name('area_degree3.json').read_text())
outs=[]
for j in J:
 edges=j['edges']
 def dual(z):
  mu=z[:11];lam=z[11];v=2*math.pi*(sum(mu)-lam)
  for i,k in edges:
   b=mu[i]+mu[k];t=math.acos(np.clip(b/(R*R),-1,1));v+=R*R*math.sin(t)-b*t
  v+=sum(np.max(F+lam*w-mu[i]*a) for i in range(9))
  return v
 z=np.r_[j['mu'],max(0,j['lambda'])]
 o=minimize(dual,z,method='Powell',bounds=[(-1,1)]*11+[(0,2)],options={'maxiter':100,'ftol':1e-9,'xtol':1e-8})
 print(j['q'],j['edge'],dual(z),o.fun,flush=True)
 outs.append({'q':j['q'],'edge':j['edge'],'dual':float(o.fun),'z':o.x.tolist(),'success':bool(o.success)})
Path(__file__).with_suffix('.json').write_text(json.dumps(outs,indent=2))
