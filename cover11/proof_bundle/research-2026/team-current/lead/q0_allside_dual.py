"""All21side matching enforced: theta11faces+9switches. FINITE GRID diagnostic only."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
from pathlib import Path
import numpy as np,json,math,time
P=Path(__file__).parent
src=(P/'q0_theta_candidate25_dual.py').read_text().split('\nK=19;arows=[];rhs=[]')[0];exec(src)
# Eliminate every first/second side multiplier, including9 boundary edges.
fixed=list(range(side,side+21))+list(range(lin,lin+21))
SB=[]
for i in range(9):
 j=(i+1)%9;ei=edges.index(tuple(sorted((i,j))));bs0=np.array([np.linspace(math.asin(t),math.pi/2,161) for t in grid]);yy=np.divide(grid[:,None],np.sin(bs0),out=np.zeros_like(bs0),where=np.sin(bs0)>1e-15)
 # t=0: b=0 can have any y; explicitly sample its radius branch.
 bs0[0,:]=0;yy[0,:]=np.linspace(0,1,161)
 vv=R*R*yy**2*np.sin(2*bs0)/2;M=np.zeros((*vv.shape,nz));M[:,:,i]+=bs0;M[:,:,j]+=bs0;M[:,:,kap+ei]-=bs0;M[:,:,cl+i]+=2*bs0;M[:,:,side+ei]-=grid[:,None]**2;M[:,:,lin+ei]-=grid[:,None]
 for k in [2*i+1,2*j]:M[:,:,rr+k]+=yy**2;M[:,:,lin+21+k]+=yy
 SB.append((vv,M))
# Actual witness joint row (calibration retained under allside coupling)
VC2=VC+sum(factors[11+i][0][-1] for i in range(9));MC2=MC+sum(factors[11+i][1][-1] for i in range(9));assert max(abs(MC2[fixed]))<1e-13

def separate_all(z):
 st=[];si=[]
 for vv,MM in SB:
  vals=vv+MM@z;ii=np.argmax(vals,axis=1);st.append(vals[np.arange(m),ii]);si.append(ii)
 tensors=[]
 for fi in range(11):
  v=areas+rowsF[fi]@z
  if fi<9:v=v+st[fi][trip[:,2]]
  T=np.full(m**3,-np.inf);I=np.full(m**3,-1,dtype=int);order=np.argsort(v,kind='stable');T[flatidx[order]]=v[order];I[flatidx[order]]=order;tensors.append((T.reshape(m,m,m),I.reshape(m,m,m)))
 W=[np.max(T,axis=2) for T,I in tensors[:9]];arg=[np.argmax(T,axis=2) for T,I in tensors[:9]];A,ba=path_transfer(W[:4]);B,bb=path_transfer(W[4:]);best=-np.inf
 for h in range(m):
  val,cp=cycle([tensors[9][0][:,:,h],B.T,tensors[10][0][:,:,h].T,A.T])
  if val>best:best=val;bestcp=cp;besth=h
 a0,b0,b4,a4,_=bestcp;h=besth;pa=path_recover(ba,a0,a4);pb=path_recover(bb,b4,b0);inds=[]
 for i,(u,v) in enumerate(zip(pa[:-1]+pb[:-1],pa[1:]+pb[1:])):inds.append(int(tensors[i][1][u,v,arg[i][u,v]]))
 inds += [int(tensors[9][1][a0,b0,h]),int(tensors[10][1][a4,b4,h])];assert min(inds)>=0
 V=sum(areas[ii] for ii in inds);M=sum(rowsF[fi][ii] for fi,ii in enumerate(inds))
 for i in range(9):
  t=trip[inds[i],2];k=si[i][t];V+=SB[i][0][t,k];M+=SB[i][1][t,k]
 assert max(abs(M[fixed]))<1e-12;assert abs(V+M@z-best)<1e-9
 if VC2+MC2@z>best:V=VC2;M=MC2.copy();best=V+M@z
 vals=[best];cuts=[(V,M)]
 for vv,MM in factors[20:]:
  q=vv+MM@z;i=int(np.argmax(q));vals.append(q[i]);cuts.append((vv[i],MM[i]))
 return vals,cuts
K=10;arows=[];rhs=[]
def add(cuts):
 for fi,(v,M) in enumerate(cuts):
  a=np.zeros(nz+K);a[:nz]=M;a[nz+fi]=-1;arows.append(a);rhs.append(-v)
bounds=[(-3,3)]*kap+[(0,3)]*(ne+2)+[(-3,3)]*48+[(None,None)]*K;bounds[eta]=(0,0)
for k in fixed:bounds[k]=(0,0)
z0=np.array(json.loads((P/'q0_theta_candidate25_dual_0_4.json').read_text())['z']);z0[fixed]=0
vals,cuts=separate_all(z0);add(cuts);best=float(const@z0+sum(vals));bestz=z0.copy();t0=time.time();print('ALLSIDE_CALIBRATION',best,flush=True)
for it in range(350):
 sol=linprog(np.r_[const,np.ones(K)],A_ub=np.array(arows),b_ub=np.array(rhs),bounds=bounds,method='highs');assert sol.success,sol.message
 z=sol.x[:nz];vals,cuts=separate_all(z);ub=float(const@z+sum(vals));add(cuts)
 if ub<best:best=ub;bestz=z.copy()
 if it%20==0:print('ALLSIDE',it,sol.fun,best,time.time()-t0,flush=True)
 if ub-sol.fun<2e-6:break
out={'R':R,'sample_upper':best,'lp_lower':float(sol.fun),'iterations':it+1,'side_nodes':m,'switch_angle_nodes':161,'z':bestz.tolist(),'scope':'finite sidegrid and switchangle grid; all21side matching exact, NOT continuum certificate'}
(P/'q0_allside_dual_0_4.json').write_text(json.dumps(out,indent=2));print('RESULT',best,flush=True)
