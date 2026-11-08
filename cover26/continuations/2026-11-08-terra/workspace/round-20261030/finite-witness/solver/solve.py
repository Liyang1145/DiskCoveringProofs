"""Bounded finite set-cover prototype. NO geometric mask-completeness claim."""
import argparse,gzip,hashlib,json,math,time
from pathlib import Path
import numpy as np
from scipy.sparse import coo_matrix
from scipy.optimize import milp,Bounds,LinearConstraint,linprog
if not __debug__:raise RuntimeError('Assertions must be enabled')
def read(p):
 raw=Path(p).read_bytes()
 obj=json.loads(gzip.decompress(raw) if raw[:2]==b'\x1f\x8b' else raw)
 n=len(obj['points']);full=(1<<n)-1
 masks=sorted(set(int(x,16) for x in obj['masks'] if int(x,16)),reverse=True)
 assert n and masks and all(m&~full==0 for m in masks)
 return raw,n,masks

def prepare(n,masks):
 incidence=[[] for _ in range(n)]; rows=[];cols=[]
 for j,m in enumerate(masks):
  b=m
  while b:
   x=b&-b; i=x.bit_length()-1; b-=x;rows.append(i);cols.append(j);incidence[i].append(j)
 mat=coo_matrix((np.ones(len(rows)),(rows,cols)),shape=(n,len(masks))).tocsc()
 return incidence,mat

def main():
 a=argparse.ArgumentParser();a.add_argument('input');a.add_argument('--target',type=int,default=26);a.add_argument('--milp-seconds',type=float,default=25);a.add_argument('--tree-seconds',type=float,default=25);a.add_argument('--max-nodes',type=int,default=10000);a.add_argument('--certificate');a.add_argument('--cover');q=a.parse_args()
 raw,n,masks=read(q.input);inc,A=prepare(n,masks)
 print('points',n,'unique nonempty masks',len(masks),'target',q.target,flush=True)
 s=milp(np.ones(len(masks)),integrality=np.ones(len(masks)),bounds=Bounds(np.zeros(len(masks)),np.ones(len(masks))),constraints=LinearConstraint(A,np.ones(n),np.full(n,np.inf)),options={'time_limit':q.milp_seconds})
 print('MILP status',s.status,'objective',s.fun,'dual_bound',getattr(s,'mip_dual_bound',None),'diagnostic only',flush=True)
 if s.x is not None:
  chosen=[masks[i] for i,v in enumerate(s.x) if v>0.5]; union=0
  for m in chosen:union|=m
  if union==(1<<n)-1:
   print('EXACT finite-mask cover found:',len(chosen),'masks',flush=True)
   if q.cover:
    proof={'schema':'finite-set-cover-cover-v1','input_sha256':hashlib.sha256(raw).hexdigest(),'n':n,'masks':[hex(m) for m in chosen]}
    Path(q.cover).write_text(json.dumps(proof,indent=2)+'\n',encoding='utf8')
   if len(chosen)<=q.target:
    print('Target cannot be excluded for this mask instance; no search started.',flush=True);return
 L=linprog(-np.ones(n),A_ub=A.T,b_ub=np.ones(len(masks)),bounds=(0,None),method='highs',options={'time_limit':min(10,q.milp_seconds)})
 print('LP status',L.status,'objective',None if L.fun is None else -L.fun,flush=True)
 weights=[0]*n if L.x is None else [max(0,math.floor(float(v)*10**8)) for v in L.x]
 deadline=time.monotonic()+q.tree_seconds; nodes=0
 def bits(b):
  while b:
   a=b&-b;yield a.bit_length()-1;b-=a
 def solve(U,k):
  nonlocal nodes
  nodes+=1
  if nodes>q.max_nodes or time.monotonic()>deadline:raise TimeoutError
  if not U:return None
  points=list(bits(U)); total=sum(weights[i] for i in points)
  peak=max((sum(weights[i] for i in bits(m&U)) for m in masks),default=0)
  if total>k*peak:return {'kind':'weight'}
  conflict=[]
  for i in points:
   v=0
   for j in inc[i]:v|=masks[j]&U
   conflict.append((v.bit_count(),i,v))
  # Greedy packing: no input mask covers two chosen points.
  packing=[];remaining=U;conf_by_i={i:v for _,i,v in conflict}
  while remaining:
   i=min(bits(remaining),key=lambda x:(conf_by_i[x]&remaining).bit_count())
   packing.append(i);remaining &= ~conf_by_i[i];remaining &= ~(1<<i)
   if len(packing)>k:return {'kind':'packing','points':packing}
  if k==0:return {'kind':'packing','points':[points[0]]}
  # Only distinct projections onto the remaining universe are needed.
  pivot=min(points,key=lambda i:len({masks[j]&U for j in inc[i]}))
  options=sorted({masks[j]&U for j in inc[pivot]},reverse=True)
  children=[]
  for opt in options:
   child=solve(U&~opt,k-1)
   if child is None:return None
   children.append(child)
  return {'kind':'branch','point':pivot,'children':children}
 try: tree=solve((1<<n)-1,q.target)
 except TimeoutError:tree=None; print('PENDING: node or time limit reached',flush=True)
 print('searched nodes',nodes,'certificate produced',tree is not None,flush=True)
 if tree is not None:
  cert={'schema':'finite-set-cover-tree-v1','input_sha256':hashlib.sha256(raw).hexdigest(),'n':n,'target':q.target,'integer_weights':weights,'tree':tree,'scope':'Finite set-cover only. Geometric coverage requires separate independently verified exhaustive mask generation.'}
  path=Path(q.certificate or 'finite-cover-certificate.json');path.write_text(json.dumps(cert,separators=(',',':')),encoding='utf8');print('certificate',path,flush=True)
 else:print('NO PROOF: absence of certificate is not a lower bound.',flush=True)
if __name__=='__main__':main()
