"""Numeric calibration of chain3-point variance identity, not sharp bound certification."""
from pathlib import Path
import numpy as np,json,math
P=Path(__file__).parent;q=P/'q0_exact_closure_radius.py';ns={'__file__':str(q)};exec(q.read_text().split('edges=sorted')[0],ns);c=ns['c'];r=.3799838531198388;roots=[]
for i in range(9):
 a,b=c[i],c[(i+1)%9];m=(a+b)/2;d=np.linalg.norm(b-a);n=np.array([-(b-a)[1],(b-a)[0]])/d;k=math.sqrt(r*r-d*d/4)
 roots.append(min([m+k*n,m-k*n],key=np.linalg.norm))
ids=[4,6,8];p=np.array(roots)[ids];h=c[10];lam=np.linalg.solve(np.vstack([p.T,np.ones(3)]),np.r_[h,1])
assert min(lam)>0
v=sum(lam[i]*lam[j]*np.sum((p[i]-p[j])**2) for i in range(3) for j in range(i))
M=np.column_stack([p[1]-p[0],p[2]-p[0]]);cross=np.linalg.det(M);lengths=[np.sum((p[i]-p[j])**2) for i,j in [(0,1),(1,2),(2,0)]];F=math.prod(lengths)-4*r*r*cross*cross
# Rational lambda near candidate is a valid global fixed-weight inequality, NOT candidate tight exactly
num=np.round(lam*10**9).astype(int);num[-1]=10**9-sum(num[:-1]);lr=num/1e9
vr=sum(lr[i]*lr[j]*np.sum((p[i]-p[j])**2) for i in range(3) for j in range(i))
errs=[]
for z in [h,np.array([.1,.2]),np.array([0.,0.])]:
 lhs=sum(lr[i]*np.sum((z-p[i])**2) for i in range(3));rhs=vr+np.sum((z-lr@p)**2);errs.append(abs(lhs-rhs))
assert max(errs)<1e-15
out={'scope':'numeric saved rational rings at candidate floating allowance; no certification','edge_indices':ids,'points':p.tolist(),'weights':lam.tolist(),'variance_minus_r2':float(v-r*r),'circum_polynomial':F,'rational_weights_numerators':num.tolist(),'denominator':10**9,'rational_variance_minus_r2':float(vr-r*r),'identity_error':max(errs)}
(P/'r20_chain_variance.json').write_text(json.dumps(out,indent=2));print(out)
