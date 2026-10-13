"""Bounded diagnostic: new dual for entire sector2 degeneracy facet, not grid certification.
Fixed R0=.38; alpha2=pi,u2=v2=t in[75/76,1]. Old unrestricteddual cannot excludefacet.
"""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
from pathlib import Path
import sys,time,json,numpy as np
from scipy.optimize import linprog
P=Path(__file__).parent;sys.argv=['x','0','4']
src=(P/'q0_closure_dual.py').read_text();marker='\n K=len(factors);rows=[];rhs=[];';assert src.count(marker)==1
src=src.split(marker)[0]
src=src.replace('N=36;NR=12;NA=96','N=24;NR=8;NA=64')
ns={'__file__':str(P/'q0_closure_dual.py')};exec(src,ns)
factors=ns['factors'];const=ns['const'];nz=ns['nz'];R=ns['R'];pi=np.pi
a,u,v=ns['grid'].T;Q=(u-v)**2+4*u*v*np.sin(a/2)**2;h=R*np.sqrt(Q)/2;k=np.sqrt(1-h*h)
mask=(Q>=4*np.sin(pi-8*np.arcsin(R))**2/R**2)&(u*v*(k*np.sin(a)-h*np.cos(a))>=np.maximum.reduce([np.full_like(u,(75/76)**2),u*u,v*v])*h-1e-14)
for fi in range(20,29):
 vv,MM=factors[fi];factors[fi]=(vv[mask],MM[mask])
print('inwardmask',sum(mask),'of',len(mask),flush=True)
i=2;t=np.linspace(75/76,1,101);w=2*np.arcsin(R*t);v=(w-np.sin(w))/2;M=np.zeros((len(t),nz));M[:,i]=-pi;M[:,32+2*i]=-t*t;M[:,33+2*i]=-t*t;M[:,94+2*i]=-t;M[:,95+2*i]=-t;M[:,71]=w;M[:,112+(i-1)%9]=w/2;M[:,112+i]=w/2;factors[20+i]=(v,M)
K=len(factors);arows=[];rhs=[];used=[set() for _ in factors]
def add(fi,idx):
 if idx in used[fi]:return
 used[fi].add(idx);vv,MM=factors[fi];a=np.zeros(nz+K);a[:nz]=MM[idx];a[nz+fi]=-1;arows.append(a);rhs.append(-vv[idx])
def sep(z):
 vals=[]
 for fi,(v,M) in enumerate(factors):
  f=v+M@z;idx=int(np.argmax(f));vals.append(f[idx]);add(fi,idx)
 return float(const@z+sum(vals))
bounds=[(-3,3)]*50+[(0,3)]*23+[(-3,3)]*48+[(None,None)]*K;bounds[72]=(0,0)
z0=np.array(json.loads((P/'q0_closure_dual_0_4.json').read_text())['z']);best=sep(z0);bestz=z0.copy();t0=time.time()
for it in range(180):
 sol=linprog(np.r_[const,np.ones(K)],A_ub=np.array(arows),b_ub=rhs,bounds=bounds,method='highs');assert sol.success,sol.message
 z=sol.x[:nz];val=sep(z)
 if val<best:best=val;bestz=z.copy()
 if it%20==0:print(it,'sample',best,'LP',sol.fun,'seconds',time.time()-t0,flush=True)
 if best<pi-.005 and val-sol.fun<.0005:break
out={'scope':'finite sample diagnostic only, NO continuumclaim; conditionalalpha2pi,u=v=t','start':0,'span':4,'sector':2,'R':R,'sample_upper':best,'lp_value':float(sol.fun),'iterations':it+1,'z':bestz.tolist(),'faces':ns['faces'],'edges':ns['edges']}
(P/'middle_sector_inward_dual_proposal.json').write_text(json.dumps(out,indent=2));print('RESULT',best,sol.fun,it+1,flush=True)
