import numpy as np,math,time,json,sys
from scipy.sparse import csc_matrix
from scipy.optimize import milp,LinearConstraint,Bounds,linprog
from pathlib import Path
T=time.monotonic();r=.225
# Offset square-lattice rows, denominator 4000, 1/20 spacing.
scale=4000;P=[]
for y in range(-4000,4001,200):
 for x in range(-4000+(100 if (y//200)%2 else 0),4001,200):
  if x*x+y*y<=scale*scale:P.append((x,y))
for j in range(100):
 x=round(3999*math.cos(2*math.pi*j/100));y=round(3999*math.sin(2*math.pi*j/100))
 assert x*x+y*y<=scale*scale
 if (x,y) not in P:P.append((x,y))
P=np.array(P,dtype=np.int32);print('points',len(P),flush=True)
# Find all geometrically possible pair-circle centers.
V=P[:,None,:].astype(float)-P[None,:,:];D=(V*V).sum(axis=2);I,J=np.where((D>0)&(D<=(2*r*scale)**2)&(np.tril(np.ones(D.shape,dtype=bool),-1)));print('pairs',len(I),'time',round(time.monotonic()-T,2),flush=True)
delta=V[I,J];dist=np.sqrt(D[I,J]);mid=(P[I]+P[J])/2;h=np.sqrt(np.maximum(0,(r*scale)**2-dist**2/4)); normal=np.stack([-delta[:,1],delta[:,0]],axis=1)/dist[:,None];C=np.concatenate((P.astype(float),mid+h[:,None]*normal,mid-h[:,None]*normal))
M=set()
for first in range(0,len(C),256):
 ds=((C[first:first+256,None,:]-P[None,:,:])**2).sum(axis=2)
 for covered in ds<=(r*scale)**2+1e-5:
  M.add(int.from_bytes(np.packbits(covered,bitorder='little').tobytes(),'little'))
 if time.monotonic()-T>45: print('geometry timed out incomplete');sys.exit(2)
print('unique_masks',len(M),'time',round(time.monotonic()-T,2),flush=True)
ordered=sorted(M,key=int.bit_count,reverse=True);inv=[set() for _ in P];kept=[]
for z in ordered:
 ind=[]; b=z
 while b:
  k=b&-b;ind.append(k.bit_length()-1);b-=k
 short=min((inv[i] for i in ind),key=len)
 if any(z&kept[j]==z for j in short):continue
 j=len(kept);kept.append(z)
 for i in ind: inv[i].add(j)
 if time.monotonic()-T>55:print('dominance timeout');sys.exit(2)
print('maximal',len(kept),'time',round(time.monotonic()-T,2),flush=True)
rows=[];cols=[]
for j,z in enumerate(kept):
 while z:
  b=z&-z;rows.append(b.bit_length()-1);cols.append(j);z-=b
A=csc_matrix((np.ones(len(rows)),(rows,cols)),shape=(len(P),len(kept)));A.indices=A.indices.astype(np.int32);A.indptr=A.indptr.astype(np.int32)
lp=linprog(np.ones(len(kept)),A_ub=-A,b_ub=-np.ones(len(P)),bounds=(0,1),method='highs',options={'time_limit':10})
print('LP',lp.status,lp.fun,'time',round(time.monotonic()-T,2),flush=True)
remaining=max(1,89-(time.monotonic()-T))
result=milp(np.ones(len(kept)),integrality=np.ones(len(kept)),bounds=Bounds(0,1),constraints=LinearConstraint(A,1,np.inf),options={'time_limit':remaining})
print('MILP',result.status,'objective',result.fun,'dualbound',getattr(result,'mip_dual_bound',None),'gap',getattr(result,'mip_gap',None),'time',round(time.monotonic()-T,2),flush=True)
(p:=Path(__file__).resolve().parent/'preliminary.json').write_text(json.dumps({'points':P.tolist(),'radius':'9/40','scale':scale,'masks':[hex(z) for z in kept],'solver_status':int(result.status),'objective':None if result.fun is None else float(result.fun),'dualbound':None if getattr(result,'mip_dual_bound',None) is None else float(result.mip_dual_bound)},indent=1),encoding='utf8')
