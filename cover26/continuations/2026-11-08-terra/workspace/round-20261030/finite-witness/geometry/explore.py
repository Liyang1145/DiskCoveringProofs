import numpy as np, math,time
from scipy.optimize import milp,LinearConstraint,Bounds,linprog
from scipy.sparse import csc_matrix
r=9/40
rings=[(1,80),(.8,64),(.6,48),(.4,32),(.2,16)]
P=np.concatenate([np.array([[rho*math.cos(2*math.pi*(k+(j%2)*.5)/n),rho*math.sin(2*math.pi*(k+(j%2)*.5)/n)] for k in range(n)]) for j,(rho,n) in enumerate(rings)] + [np.array([[0.,0.]])]); m=len(P)
t=time.monotonic(); centers=[*P];
for i in range(m):
 for j in range(i):
  v=P[i]-P[j]; d=np.linalg.norm(v)
  if 0<d<=2*r:
   q=(P[i]+P[j])/2; h=math.sqrt(max(0,r*r-d*d/4)); n=np.array([-v[1],v[0]])/d
   centers.extend([q+h*n,q-h*n])
M=set()
for pos in range(0,len(centers),1024):
 C=np.array(centers[pos:pos+1024]); ds=((C[:,None,:]-P[None,:,:])**2).sum(axis=2)
 for covered in ds<=r*r+1e-12:
  M.add(sum(1<<int(i) for i in np.flatnonzero(covered)))
M.discard(0); print('points',m,'centers',len(centers),'masks',len(M),'time',round(time.monotonic()-t,2),flush=True)
# Maximal sets by using inverted lists of already seen larger sets.
ordered=sorted(M,key=int.bit_count,reverse=True); inv=[set() for _ in range(m)]; kept=[]
for mask in ordered:
 indices=[i for i in range(m) if mask>>i&1]; shortlist=min((inv[i] for i in indices),key=len)
 if any(mask&kept[k]==mask for k in shortlist): continue
 idx=len(kept); kept.append(mask)
 for i in indices: inv[i].add(idx)
print('maximal',len(kept),'time',round(time.monotonic()-t,2),flush=True)
rows=[];cols=[]
for j,mask in enumerate(kept):
 while mask:
  b=mask & -mask;i=b.bit_length()-1;rows.append(i);cols.append(j);mask-=b
A=csc_matrix((np.ones(len(rows)),(rows,cols)),shape=(m,len(kept)))
A.indices=A.indices.astype(np.int32); A.indptr=A.indptr.astype(np.int32)
lp=linprog(np.ones(len(kept)),A_ub=-A,b_ub=-np.ones(m),bounds=(0,1),method='highs',options={'time_limit':15})
print('LP',lp.status,lp.fun, 'time',round(time.monotonic()-t,2),flush=True)
result=milp(np.ones(len(kept)),integrality=np.ones(len(kept)),bounds=Bounds(0,1),constraints=LinearConstraint(A,1,np.inf),options={'time_limit':60})
print('MILP status',result.status,'objective',result.fun,'dualbound',getattr(result,'mip_dual_bound',None),'gap',getattr(result,'mip_gap',None),'time',round(time.monotonic()-t,2),flush=True)
