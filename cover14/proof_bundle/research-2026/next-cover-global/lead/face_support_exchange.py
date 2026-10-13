"""Bounded adaptive support cuts for one allface dual; no global bound from numerical separation."""
from all_face_consistency_probe import *
from scipy.optimize import minimize
import inspect
source=inspect.getsource(solve).replace('def solve(q,edges,faces,nfg=11):','def exchange_solve(q,edges,faces,extra,nfg=11):')
source=source.replace('M=2*q*len(grid)+nf*len(samples)+ne*(len(grid)+1)','M=2*q*len(grid)+nf*len(samples)+sum(len(es)for es in extra)+ne*(len(grid)+1)')
source=source.replace('for ts,A in samples:','for ts,A in samples+[(t,envelope(t))for t in extra[f]]:')
exec(source)
if __name__=='__main__':
 start=time.time();fam='10/4';idx=547;q=10;faces=json.loads((P/'k10-catalogue-corrected.json').read_text())[fam][idx]['faces'];edges=sorted({tuple(sorted(e))for f in faces for e in combinations(f,2)});extra=[[]for f in faces];runs=[]
 grid=np.linspace(0,math.pi,11);tsall=np.array([ts for ts in product(grid,repeat=3)if sum(ts)<=2*math.pi+1e-12]);env=np.array([envelope(ts)for ts in tsall])
 for iteration in range(9):
  row=exchange_solve(q,edges,faces,extra);w=np.array(row['weights']);pp=np.array(row['face_potentials']);supports=np.array(row['face_supports']);worst=[]
  for f in range(len(faces)):
   obj=lambda t:float(pp[f]@t-w[f]*envelope(t));values=w[f]*env-tsall@pp[f];starts=[tsall[j]for j in np.argsort(values)[-3:]]+extra[f][-2:];best=None
   for x in starts:
    a=minimize(obj,x,method='SLSQP',bounds=[(0,math.pi)]*3,constraints=[{'type':'ineq','fun':lambda t:2*math.pi-sum(t)}],options={'maxiter':80,'ftol':1e-11})
    if sum(a.x)<=2*math.pi+1e-8 and (best is None or a.fun<best.fun):best=a
   assert best is not None;v=-best.fun-supports[f];worst.append(v)
   if v>1e-7:extra[f].append(best.x.tolist())
  row.update(family=fam,index=idx,exchange_iteration=iteration,face_violation_sum=float(sum(max(0,v)for v in worst)),face_violation_max=float(max(worst)),extra_samples=sum(map(len,extra)));runs.append(row);print(iteration,'sampled',row['sampled_lp_not_bound'],'faceviolation',row['face_violation_sum'],'cuts',row['extra_samples'],flush=True);(P/'face-support-exchange.json').write_text(json.dumps({'status':'numeric_separation_proposals_only','runs':runs,'extra_face_samples':extra,'seconds':time.time()-start},indent=2))
  if max(worst)<1e-6:break
