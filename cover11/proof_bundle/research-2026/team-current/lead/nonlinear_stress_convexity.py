"""Bounded legal directional curvature test; decide whether global convexity route is plausible."""
from pathlib import Path
import numpy as np,json,warnings
from scipy.special import logsumexp
warnings.filterwarnings('ignore')
P=Path(__file__).parent;z={'__file__':str(P/'angle_stress_probe.py')};exec((P/'angle_stress_probe.py').read_text().split('y0=np.zeros(29)')[0],z)
N,a0,branches,lam,mu,act,domain=[z[k] for k in ['N','a0','branches','lam','mu','act','domain']];n=N.shape[1];rng=np.random.default_rng(843)
def fun(y):
 d=domain(y)
 if not np.all(np.isfinite(d)) or min(d)<.002:return None
 g,c=branches(a0+N@y);v=.1*logsumexp(10*g[act],b=lam)+mu@c+sum(c[13:]**2)
 return float(v) if np.isfinite(v) else None
best=None;tries=0
for radius in [.05,.15,.3,.6,1.]:
 valid=0
 for attempt in range(5000):
  y=rng.normal(size=n);y*=radius/np.linalg.norm(y);v0=fun(y)
  if v0 is None:continue
  valid+=1
  for k in range(12):
   v=rng.normal(size=n);v/=np.linalg.norm(v);h=1e-4;vp=fun(y+h*v);vm=fun(y-h*v)
   if vp is None or vm is None:continue
   d2=(vp+vm-2*v0)/h**2
   if best is None or d2<best['d2']:
    best={'radius':radius,'d2':d2,'y':y.tolist(),'direction':v.tolist(),'min_domain':float(min(domain(y))),'stress':v0}
  if best['d2']<-.1 or valid>=100:break
 print('radius',radius,'valid',valid,'minimumcurvature',best['d2'],flush=True)
 if best['d2']<-.1:break
rows=[]
for h in [1e-3,1e-4,5e-5]:
 y=np.array(best['y']);v=np.array(best['direction']);rows.append({'h':h,'d2':(fun(y+h*v)+fun(y-h*v)-2*fun(y))/h**2})
(P/'nonlinear_stress_convexity.json').write_text(json.dumps({'scope':'numeric directional curvature; negative witness if present defeats convexity only, not stress positivity','best':best,'controls':rows},indent=2));print(rows)
