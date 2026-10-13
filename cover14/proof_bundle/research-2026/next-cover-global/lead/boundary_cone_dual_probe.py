"""Sampled LP only: all-face exact envelopes with independentlyallocatededgepotentials."""
from joint_innernorm_probe import *
from itertools import product
import time

def envelope(ts,mask=()):
 B=sum(ts);a=sum(math.sin(t)for t in ts);loss=.5*min(1-math.cos(t)for t in ts)*abs(B-math.pi)
 if math.pi+1e-10<B<2*math.pi-1e-10 and a>1e-10:
  b=sum(math.sin(u+v)for u,v in combinations(ts,2));c=math.sin(B);x=max(0,min(1,(b+math.sqrt(max(0,b*b-4*a*c)))/(2*a)));loss=max(loss,(1-x)*a)
 if B<math.pi and B+min(ts)>=math.pi-1e-13:
  d=(math.pi-B)/2;loss=max(loss,min(2*math.sin(t)*math.sin(t/2)*math.sin(d)/math.cos(t/2-d)for t in ts))
 X=min([1.]+[1/(math.cos(ts[j])+r/math.sqrt(1-r*r)*math.sin(ts[j]))for j in mask if math.cos(ts[j])+r/math.sqrt(1-r*r)*math.sin(ts[j])>1])
 return min(r*r*(a-loss),r*r*X*a)

def solve(q,edges,faces,nfg=11):
 nf=len(faces);ne=len(edges);ee=[[tuple(sorted(e))for e in combinations(f,2)]for f in faces];inc=[[(f,ee[f].index(e))for f in range(nf)if e in ee[f]]for e in edges]
 iw=16;ip=iw+nf;ib=ip+3*nf;ie=ib+q;iff=ie+ne;N=iff+nf
 grid=np.linspace(0,math.pi,61);fg=np.linspace(0,math.pi,nfg);samples=[(ts,envelope(ts))for ts in product(fg,repeat=3)if sum(ts)<=2*math.pi+1e-12];M=2*q*len(grid)+nf*len(samples)+ne*(len(grid)+1);mat=lil_matrix((M,N));rhs=np.zeros(M);at=0
 for j in range(q):
  for t in grid:
   h=min(float(a)+float(k)*t for a,k in lines)
   mat[at,j]=-t;mat[at,14]=bv(t);mat[at,15]=h;mat[at,ib+j]=-1;rhs[at]=-fval(t,0);at+=1
   mat[at,j]=-t;mat[at,14]=An;mat[at,15]=h;mat[at,ib+j]=-1;rhs[at]=-cAn;at+=1
 for f in range(nf):
  mask=[j for j,e in enumerate(ee[f])if len(inc[edges.index(e)])==1]
  for ts,_ in samples:
   A=envelope(ts,mask)
   mat[at,iw+f]=A
   for k,t in enumerate(ts):mat[at,ip+3*f+k]=-t
   mat[at,iff+f]=-1;at+=1
 for k,(u,v)in enumerate(edges):
  for t in grid:
   a=r*r*math.sin(t);mat[at,u]=-t;mat[at,v]=-t
   for f,j in inc[k]:mat[at,iw+f]=-a;mat[at,ip+3*f+j]=t
   mat[at,ie+k]=-1;rhs[at]=-a;at+=1
  for f,j in inc[k]:mat[at,iw+f]=1
  rhs[at]=1;at+=1
 obj=np.r_[np.full(14,2*math.pi),-2*math.pi,-2*math.pi,np.zeros(4*nf),np.ones(q+ne+nf)]
 lp=linprog(obj,A_ub=mat.tocsr(),b_ub=rhs,bounds=[(None,None)]*14+[(0,None)]*2+[(0,1)]*nf+[(None,None)]*(3*nf+q+ne+nf),method='highs');assert lp.success
 return {'sampled_lp_not_bound':float(lp.fun-math.pi),'potentials':lp.x[:14].tolist(),'nu':float(lp.x[14]),'lambda':float(lp.x[15]),'weights':lp.x[iw:ip].tolist(),'face_potentials':lp.x[ip:ib].reshape(nf,3).tolist(),'face_supports':lp.x[iff:].tolist(),'grid_size':nfg}

