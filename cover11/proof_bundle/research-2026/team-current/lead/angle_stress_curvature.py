"""Legal-domain curvature test for proposed single stress; ignores invalid SLSQP trials."""
from pathlib import Path
import numpy as np,json
P=Path(__file__).parent
zz={'__file__':str(P/'angle_stress_probe.py')};exec((P/'angle_stress_probe.py').read_text().split('y0=np.zeros(29)')[0],zz)
lag,domain,N,a0=zz['lag'],zz['domain'],zz['N'],zz['a0'];n=N.shape[1];o=np.zeros(n);base=lag(o);out={}
for h in [1e-4,5e-5]:
 H=np.zeros((n,n))
 for i in range(n):
  e=np.eye(n)[i]*h;H[i,i]=(lag(e)+lag(-e)-2*base)/h**2
  for j in range(i):
   f=np.eye(n)[j]*h;H[i,j]=H[j,i]=(lag(e+f)+lag(-e-f)-lag(e-f)-lag(-e+f))/(4*h*h)
 ev,vec=np.linalg.eigh(H);v=vec[:,0];rows=[]
 for t in [-.01,-.001,-.0001,.0001,.001,.01]:
  y=t*v;assert min(domain(y))>.1
  rows.append({'t':t,'stress_change':lag(y)-base,'min_domain':float(min(domain(y))),'angles':(a0+N@y).tolist()})
 out[str(h)]={'eigenvalues':ev.tolist(),'legal_probe':rows};print(h,ev[:4],[(x['t'],x['stress_change']) for x in rows])
(P/'angle_stress_curvature.json').write_text(json.dumps({'scope':'numeric failure witness for ONE proposed global stress extension, NOT feasible shape counterexample or proof','results':out},indent=2))
