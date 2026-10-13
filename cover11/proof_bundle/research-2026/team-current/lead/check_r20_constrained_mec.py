"""Independent known-answer controls, not continuum covering certification."""
import json, numpy as np
from scipy.optimize import minimize
from pathlib import Path
cases=[('diameter',[[-.5,0],[.5,0]],[.5,.5],.6,.25),
 ('triangle',[[.5,0],[-.25,np.sqrt(3)/4],[-.25,-np.sqrt(3)/4]],[1/3]*3,.6,.25),
 ('cap-single',[[.9,0]],[1],.6,.09),
 ('cap-pair',[[.9,.2],[.9,-.2]],[.5,.5],.6,.13)]
out=[]
for name,pts,weights,a,known in cases:
 X=np.array(pts); w=np.array(weights);m=w@X;v=w@np.sum(X*X,axis=1)
 dual=v-m@m+max(np.linalg.norm(m)-a,0)**2
 sol=minimize(lambda y:y[2],np.array([0.,0.,1.]),method='SLSQP',constraints=[{'type':'ineq','fun':lambda y:a*a-y[:2]@y[:2]},{'type':'ineq','fun':lambda y:y[2]-np.sum((X-y[:2])**2,axis=1)}],options={'ftol':1e-13,'maxiter':150})
 assert sol.success and abs(sol.fun-known)<1e-9 and abs(dual-known)<1e-12
 out.append(dict(case=name,analytic=known,dual=float(dual),primal_numeric=float(sol.fun),center=sol.x[:2].tolist()))
# Domain trap: three ring centers on radius r at equilateral angles.
# max dot >= r|x|/2 => nearest squared distance <= r²+|x|²-r|x| < r² for 0<|x|<r.
# Thus origin satisfies every >= inequality but is not closure(strict-uncovered).
p=Path(__file__).with_name('r20_constrained_mec_control.json')
p.write_text(json.dumps({'scope':'four finite-set known-answer calibration cases only; exact derivation in R20-RESIDUAL-TWO-CENTER.md','cases':out},indent=2))
print('4 known-answer constrained one-center controls agree; not a global bound')
