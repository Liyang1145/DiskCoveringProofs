"""Numerical spectral diagnostic of smooth adaptive scalar stress. No radius claim."""
import interval_network_envelope as k
import numpy as np,json
from pathlib import Path
H=k.arr(k.H)[:8,:8];G=k.arr(k.G8);N=k.arr(k.N);a=k.arr(k.alpha).ravel()
rows=[]
for tau in [0,.1,.25,.5,1,2,4,8,16,32,64,128]:
 M=H+2*tau*G@G.T;mu=np.linalg.eigvalsh(M).min();Q=tau*N@G.T;b=max(np.linalg.norm(Q,axis=1)/a)
 rows.append({'tau':tau,'min_eigenvalue':mu,'relative_weight_lipschitz':b,'mu_over_b':mu/b if b else 0})
(k.P/'adaptive_stress_diagnostic.json').write_text(json.dumps({'scope':'numeric pointwise only','rows':rows},indent=2));print(rows)
