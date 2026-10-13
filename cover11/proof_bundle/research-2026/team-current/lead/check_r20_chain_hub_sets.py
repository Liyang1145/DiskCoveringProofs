"""Bounded fixed-ring chain lens calibration. Numeric only, uses .38 and candidate float allowance."""
from pathlib import Path
import json, numpy as np, math
from scipy.optimize import minimize,linprog
P=Path(__file__).parent;q=P/'q0_exact_closure_radius.py';ns={'__file__':str(q)}
exec(q.read_text().split('edges=sorted')[0],ns);c=ns['c'];out=[]
for r in [.38,.3799838531198388]:
 roots=[]
 for i in range(9):
  a,b=c[i],c[(i+1)%9];m=(a+b)/2;d=np.linalg.norm(b-a);n=np.array([-(b-a)[1],(b-a)[0]])/d;k=math.sqrt(r*r-d*d/4)
  roots.append(min([m+k*n,m-k*n],key=np.linalg.norm))
 roots=np.array(roots);row={'r':r,'scope':'fixed rational saved rings; floating allowance and calculations','chains':[]}
 for chain,ih in [(range(4),9),(range(4,9),10)]:
  pp=roots[list(chain)];h=c[ih];g=np.linalg.norm(pp-h,axis=1)-r
  act=np.where(abs(g)<1e-10)[0];N=(h-pp[act]).T
  lp=linprog(np.zeros(len(act)),A_eq=np.vstack([N,np.ones(len(act))]),b_eq=[0,0,1],bounds=[(0,None)]*len(act),method='highs') if len(act) else None
  # convex norm intersection constraints:1-r for hub norm, r for witnesses
  def cons(z):return np.r_[(1-r)**2-z@z,r*r-np.sum((pp-z)**2,axis=1)]
  xy=[]
  for e in [[1,0],[-1,0],[0,1],[0,-1]]:
   sol=minimize(lambda z:np.dot(e,z),h,method='SLSQP',constraints=[{'type':'ineq','fun':cons}],options={'ftol':1e-14,'maxiter':200})
   xy.append({'e':e,'x':sol.x.tolist(),'residual':float(min(cons(sol.x))),'success':bool(sol.success)})
  row['chains'].append({'hub':ih,'candidate_margins':g.tolist(),'active':act.tolist(),'active_normals_zero_hull':None if lp is None else bool(lp.success),'supports':xy})
 out.append(row)
(P/'r20_chain_hub_sets.json').write_text(json.dumps(out,indent=2));print([(z['r'],[(a['hub'],a['active'],a['active_normals_zero_hull']) for a in z['chains']]) for z in out])
