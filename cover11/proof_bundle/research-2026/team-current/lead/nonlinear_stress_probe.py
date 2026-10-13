"""Finite mixed-curvature and legal sampling diagnostic, NOT neighborhood/global certificate."""
from pathlib import Path
import numpy as np,json
from scipy.special import logsumexp
P=Path(__file__).parent
z={'__file__':str(P/'angle_stress_probe.py')};exec((P/'angle_stress_probe.py').read_text().split('y0=np.zeros(29)')[0],z)
lag,domain,N,a0,branches,lam,mu,act=[z[k] for k in ['lag','domain','N','a0','branches','lam','mu','act']]
n=N.shape[1];o=np.zeros(n);base=lag(o);h=1e-4;H=np.zeros((n,n))
for i in range(n):
 e=np.eye(n)[i]*h;H[i,i]=(lag(e)+lag(-e)-2*base)/h**2
 for j in range(i):
  f=np.eye(n)[j]*h;H[i,j]=H[j,i]=(lag(e+f)+lag(-e-f)-lag(e-f)-lag(-e+f))/(4*h*h)
Jg=z['Jg']@N;Jc=z['Jc'][13:]@N;gbar=lam@Jg;Cov=Jg.T@(lam[:,None]*Jg)-np.outer(gbar,gbar);C=Jc.T@Jc
from scipy.linalg import null_space
Q=null_space(np.vstack([Jc,Jg-gbar]),rcond=1e-7);evker=np.linalg.eigvalsh(Q.T@H@Q);print('common kernel',Q.shape[1],evker)
params=[]
for temp in [1,.3,.1,.03,.01]:
 for rho in [1,10,100,1000]:
  ev=np.linalg.eigvalsh(H+Cov/temp+2*rho*C);params.append({'temp':temp,'rho':rho,'min_eigenvalue':float(ev[0])})
ok=[p for p in params if p['min_eigenvalue']>.02];assert ok
par=ok[0];temp=par['temp'];rho=par['rho'];print('selected',par)
def stress(y):
 g,c=branches(a0+N@y);return temp*logsumexp(g[act]/temp,b=lam)+mu@c+rho*sum(c[13:]**2)
rng=np.random.default_rng(840);b0=stress(o);samples=[]
for radius in [.001,.01,.05,.2,.5]:
 changes=[];tries=0
 while len(changes)<200 and tries<4000:
  tries+=1;v=rng.normal(size=n);y=radius*v/np.linalg.norm(v)
  try:d=domain(y)
  except (ValueError,OverflowError):continue
  if not np.all(np.isfinite(d)) or min(d)<=1e-5:continue
  value=stress(y)-b0
  if np.isfinite(value):changes.append(float(value))
 row={'radius':radius,'valid':len(changes),'tries':tries,'minimum_change':min(changes) if changes else None};samples.append(row);print(row)
out={'scope':'finite mixed-Hessian and sampling only; not remainder/neighborhood/global certificate','common_kernel_dimension_numeric':Q.shape[1],'kernel_eigenvalues':evker.tolist(),'parameter_scan':params,'chosen':par,'samples':samples,'stationarity_error':z['station']}
(P/'nonlinear_stress_probe.json').write_text(json.dumps(out,indent=2))
