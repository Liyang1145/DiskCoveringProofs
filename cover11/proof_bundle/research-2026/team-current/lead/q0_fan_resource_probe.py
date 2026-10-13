"""Fixed-dual finite positive-sidegrid hub-angle resource probe. NOT continuum upper bound."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
from pathlib import Path
import json,math,numpy as np,itertools,time
P=Path(__file__).parent
src=(P/'q0_theta_candidate25_dual.py').read_text().split('\nK=19;arows=[];rhs=[]')[0]
exec(src)
# No positive-collinear or repeated-site records in this finite diagnostic.
ok=np.all(trip>0,axis=1);tr=trip[ok];an=angles[ok];av=areas[ok];mf=[a[ok] for a in rowsF]
NB=180;delta=2*math.pi/NB
resk=np.floor(an[:,2]/delta+1e-11).astype(int)
def resource_path(triples,ks,values,m,NB):
 dp=np.full((m,m,NB+1),-np.inf)
 for i in range(m):dp[i,i,0]=0
 for vals in values:
  nxt=np.full_like(dp,-np.inf)
  for (a,b,c),k,v in zip(triples,ks,vals):
   if k<=NB:np.maximum(nxt[:,b,k:],dp[:,a,:NB+1-k]+v,out=nxt[:,b,k:])
  dp=nxt
 return dp
# Independent brute path control, repeated-resource cases included.
rng=np.random.default_rng(842);ctr=np.array(list(itertools.product(range(3),repeat=3)));ck=rng.integers(0,4,len(ctr));cv=[rng.normal(size=len(ctr)) for _ in range(3)];cd=resource_path(ctr,ck,cv,3,10);br=np.full_like(cd,-np.inf)
for rows in itertools.product(range(len(ctr)),repeat=3):
 if ctr[rows[0],1]!=ctr[rows[1],0] or ctr[rows[1],1]!=ctr[rows[2],0]:continue
 k=sum(ck[r] for r in rows)
 if k<=10:
  a=ctr[rows[0],0];b=ctr[rows[-1],1];br[a,b,k]=max(br[a,b,k],sum(cv[j][r] for j,r in enumerate(rows)))
assert np.array_equal(np.isfinite(cd),np.isfinite(br));assert np.max(abs(cd[np.isfinite(cd)]-br[np.isfinite(cd)]))<1e-12
# Candidate angle and floor-resource calibration, face ordering inferred from site IDs.
for hub,d in [(9,6),(10,7)]:
 aa0=np.array([ang0[fi,faces[fi].index(hub)] for fi in range(11) if hub in faces[fi]])
 assert len(aa0)==d and abs(sum(aa0)-2*math.pi)<1e-13
 assert NB-d<=sum(np.floor(aa0/delta))<=NB
# Known regular degree6/7 stars: exact circumradius condition and resource bins.
for d in [6,7]:
 s=math.pi/d;theta=2*math.pi/d;rho=math.cos(s)/math.cos(theta/2);assert abs(rho-1)<1e-14
 assert NB-d<=d*math.floor(theta/delta+1e-11)<=NB
out=[]
for stem in ['q0_closure_dual_0_4','q0_theta_candidate25_dual_0_4']:
 z=np.array(json.loads((P/(stem+'.json')).read_text())['z']);z[fixed]=0;t0=time.time();values=[av+M@z for M in mf]
 A=resource_path(tr,resk,values[:4],m,NB);B=resource_path(tr,resk,values[4:9],m,NB)
 # upper-window lookup U[a,b,t] = max DP[a,b,k] for t-d <=k<=t.
 def window(D,d):
  W=np.full((m,m,NB+1),-np.inf)
  for t in range(NB+1):W[:,:,t]=np.max(D[:,:,max(0,t-d):t+1],axis=2)
  return W
 AW=window(A,6);BW=window(B,7);best=-np.inf;bestdetail=None;uncon=-np.inf
 for h in range(1,m):
  ids=np.flatnonzero(tr[:,2]==h)
  if not len(ids):continue
  a=tr[ids,0];b=tr[ids,1];ax=np.floor(an[ids,1]/delta+1e-11).astype(int);bx=np.floor(an[ids,0]/delta+1e-11).astype(int)
  ta=NB-ax[:,None]-ax[None,:];tb=NB-bx[:,None]-bx[None,:]
  legal=(ta>=0)&(tb>=0)&(ta<=NB)&(tb<=NB)
  score=values[9][ids,None]+values[10][ids][None,:]
  score=score+AW[a[:,None],a[None,:],np.clip(ta,0,NB)]+BW[b[None,:],b[:,None],np.clip(tb,0,NB)]
  score[~legal]=-np.inf
  j,k=np.unravel_index(np.argmax(score),score.shape)
  if score[j,k]>best:best=float(score[j,k]);bestdetail={'hubside_index':h,'X':tr[ids[j]].tolist(),'Y':tr[ids[k]].tolist(),'budgetA':int(ta[j,k]),'budgetB':int(tb[j,k])}
  u=values[9][ids,None]+values[10][ids][None,:]+np.max(A,axis=2)[a[:,None],a[None,:]]+np.max(B,axis=2)[b[None,:],b[:,None]];uncon=max(uncon,float(np.max(u)))
 cand=float(VC+MC@z);oldvals,_,_=separate(z);other=float(const@z+sum(oldvals[1:]));row={'source':stem,'R':R,'side_nodes':m,'angle_bins':NB,'positive_side_rows':len(tr),'face_without_resources':uncon,'face_with_resources':best,'candidate_face':cand,'full_unconstrained_diagnostic':other+max(uncon,cand),'full_resource_diagnostic':other+max(best,cand),'seconds':time.time()-t0,'argmax':bestdetail,'scope':'finite positive-side grid with relaxed angular floor budgets plus mandatory genuine candidate; NOT continuum bound'};out.append(row);print(json.dumps(row),flush=True)
(P/'q0_fan_resource_probe.json').write_text(json.dumps(out,indent=2))
