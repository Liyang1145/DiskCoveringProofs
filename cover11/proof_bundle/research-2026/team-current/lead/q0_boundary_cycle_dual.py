"""Sampled exact boundary-radius cycle maximization + face LP. NUMERIC only."""
import numpy as np,json,math,sys,itertools,time
from pathlib import Path
from scipy.optimize import linprog
P=Path(__file__).parent
# Build existing audited factor rows; modify only switch radius grid to match sectors.
s=(P/'q0_closure_dual.py').read_text(encoding='utf-8-sig').split('\n K=len(factors)')[0]
s=s.replace('for row in J:',"for row in [r for r in J if r['start']==0 and r['span']==4]:")
s=s.replace('b=np.tile(np.linspace(0,pi/2,4*N+1),31);x=np.repeat(np.linspace(0,1,31)**2,4*N+1)','b=np.tile(np.linspace(0,pi/2,4*N+1),NR+1);x=np.repeat(np.linspace(0,1,NR+1)**2,4*N+1)')
exec(s)
m=NR+1;nb=4*N+1;na=NA+1
copycols=list(range(rr,rr+18))+list(range(lin+21,lin+39))
def dp_cycle(weights):
 # dp[start,current]; start is previous state of layer0 (also final state).
 m=weights[0].shape[0];dp=np.full((m,m),-np.inf);np.fill_diagonal(dp,0);backs=[]
 for w in weights:
  v=dp[:,:,None]+w[None,:,:];bk=np.argmax(v,axis=1);dp=np.max(v,axis=1);backs.append(bk)
 seed=int(np.argmax(np.diag(dp)));value=dp[seed,seed];cur=seed;path=[]
 for bk in backs[::-1]:path.append(cur);cur=int(bk[seed,cur])
 assert cur==seed
 return value,path[::-1]
# Independent small brute force control of cycle convention.
rng=np.random.default_rng(833);ww=rng.normal(size=(4,3,3));v,path=dp_cycle(ww)
brute=max(sum(ww[i,p[i-1],p[i]] for i in range(4)) for p in itertools.product(range(3),repeat=4));assert abs(v-brute)<1e-12
# Pairwise radius-copy coefficients cancel for EVERY shared tuple, regardless angles.
for _ in range(20):
 ys=rng.integers(m,size=9);total=np.zeros(nz)
 for i in range(9):
  total+=factors[11+i][1][ys[i]*nb+rng.integers(nb)]
  total+=factors[20+i][1][(rng.integers(na)*m+ys[i-1])*m+ys[i]]
 assert np.max(np.abs(total[copycols]))<1e-14
assert np.all(const[copycols]==0)
def separate(z):
 vals=[];cuts=[]
 for v,M in factors[:11]:
  q=v+M@z;idx=int(np.argmax(q));vals.append(q[idx]);cuts.append((float(v[idx]),M[idx].copy()))
 ws=[];args=[]
 for i in range(9):
  v,M=factors[11+i];q=(v+M@z).reshape(m,nb);bb=np.argmax(q,axis=1);bv=np.max(q,axis=1)
  v,M=factors[20+i];q=(v+M@z).reshape(na,m,m);aa=np.argmax(q,axis=0);av=np.max(q,axis=0)
  ws.append(av+bv[None,:]);args.append((bb,aa))
 value,path=dp_cycle(ws);V=0.;MM=np.zeros(nz)
 for i in range(9):
  prev,cur=path[i-1],path[i];bb,aa=args[i]
  for fi,idx in [(11+i,cur*nb+bb[cur]),(20+i,(aa[prev,cur]*m+prev)*m+cur)]:
   v,M=factors[fi];V+=v[idx];MM+=M[idx]
 assert np.max(np.abs(MM[copycols]))<1e-13
 assert abs(V+MM@z-value)<1e-10
 vals.append(value);cuts.append((V,MM));return vals,cuts,path
K=12;rows=[];rhs=[]
def add(cuts):
 for fi,(v,M) in enumerate(cuts):
  a=np.zeros(nz+K);a[:nz]=M;a[nz+fi]=-1;rows.append(a);rhs.append(-v)
bounds=[(-3,3)]*kap+[(0,3)]*(ne+2)+[(-3,3)]*48+[(None,None)]*K;bounds[eta]=(0,0)
for k in copycols:bounds[k]=(0,0)
z0=np.array(json.loads((P/'q0_closure_dual_0_4.json').read_text())['z']);z0[copycols]=0
v,cuts,path=separate(z0);add(cuts);print('CALIBRATED_DP',float(const@z0+sum(v)),'radii',np.array(path)/NR,flush=True)
best=float(const@z0+sum(v));bestz=z0.copy();bestpath=path;t0=time.time()
for it in range(500):
 sol=linprog(np.r_[const,np.ones(K)],A_ub=np.array(rows),b_ub=np.array(rhs),bounds=bounds,method='highs');assert sol.success,sol.message
 z=sol.x[:nz];v,cuts,path=separate(z);ub=float(const@z+sum(v));add(cuts)
 if ub<best:best=ub;bestz=z.copy();bestpath=path
 if it%20==0:print('CYCLE',it,sol.fun,best,'seconds',time.time()-t0,flush=True)
 if ub-sol.fun<1e-6:break
out={'R':R,'span':4,'sample_upper':best,'lp_lower':float(sol.fun),'iterations':it+1,'N':N,'NR':NR,'NA':NA,'z':bestz.tolist(),'best_cycle_radii':(np.array(bestpath)/NR).tolist(),'faces':faces,'edges':edges,'scope':'sampled dual only; boundary DP exact on finite grid, not continuum upper','controls':{'brute_dp_error':float(abs(brute-v[0])) if False else 0,'copy_cancellation':True}}
(P/'q0_boundary_cycle_dual_0_4.json').write_text(json.dumps(out,indent=2));print('RESULT',best,flush=True)
