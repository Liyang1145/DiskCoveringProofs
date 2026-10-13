"""Bounded triangle-block network stress scout. Numeric proposed duals only.
Each output names graph and full-domain Hessian check; no proof from optimizer.
"""
from pathlib import Path
import numpy as np,json
from scipy.optimize import minimize
P=Path(__file__).resolve().parents[1]
U=.361102963744508672616920293904;L=2*np.arcsin(U);D=9*L-2*np.pi

from network_graph import triangle,network_edges

def graph(faces):
 nf,edges=network_edges(faces)
 B=np.zeros((len(edges),nf+9))
 for e,(i,k) in enumerate(edges):B[e,i]=1;B[e,k]=-1
 return nf,edges,B

def schur(alpha,B,nf,theta):
 A=(B.T*alpha)@B
 Z=np.array([np.cos(theta),np.sin(theta)]).T
 X=-np.linalg.solve(A[:nf,:nf],A[:nf,nf:]@Z)
 diff=B@np.vstack([X,Z]);sq=np.sum(diff*diff,axis=1)
 Q=A[nf:,nf:]-A[nf:,:nf]@np.linalg.solve(A[:nf,:nf],A[:nf,nf:])
 return float(alpha@sq),sq,Q

def energy(theta,Q):
 co=np.cos(theta[:,None]-theta[None,:]);si=np.sin(theta[:,None]-theta[None,:])
 val=float(np.sum(Q*co));grad=-2*np.sum(Q*si,axis=1)
 return val,grad

def min_energy(Q):
 # y simplex maps to angles0,cumsum gaps. Fix anchor0.
 T=np.zeros((9,9))
 for i in range(1,9):T[i,:i]=-D
 base=np.arange(9)*L
 def f(y):
  v,g=energy(base+T@y,Q);return v,T.T@g
 sol=minimize(f,np.ones(9)/9,jac=True,method='SLSQP',bounds=[(0,1)]*9,constraints={'type':'eq','fun':lambda y:y.sum()-1,'jac':lambda y:np.ones(9)},options={'ftol':1e-13,'maxiter':200})
 theta=base+T@sol.x
 dd=np.minimum(abs(np.arange(9)[:,None]-np.arange(9)),9-abs(np.arange(9)[:,None]-np.arange(9)))
 weights=-2*Q*np.cos(dd*L);np.fill_diagonal(weights,0)
 M=np.diag(weights.sum(axis=1))-weights
 ev=np.linalg.eigvalsh(M)
 nonrotation=np.delete(ev,np.argmin(np.abs(ev)))
 return theta,float(sol.fun),float(nonrotation.min()),sol

def run(blocks,rounds=3):
 faces=triangle(blocks);nf,edges,B=graph(faces)
 theta=np.arange(9)*2*np.pi/9;alpha=np.ones(len(edges))/len(edges);history=[]
 for _ in range(rounds):
  def fun(al):
   val,sq,Q=schur(al,B,nf,theta);return -val,-sq
  sol=minimize(fun,alpha,jac=True,method='SLSQP',bounds=[(1e-5,1)]*len(edges),constraints={'type':'eq','fun':lambda x:x.sum()-1,'jac':lambda x:np.ones(len(x))},options={'ftol':1e-12,'maxiter':120})
  alpha=sol.x;val,sq,Q=schur(alpha,B,nf,theta)
  theta,lower,mineig,esol=min_energy(Q)
  history.append({'energy_anchor':val,'energy_min_numeric':lower,'M_nonrot_eigen_min':mineig,'radius_numeric':float(np.sqrt(max(0,lower))),'stress_success':bool(sol.success),'stress_message':str(sol.message),'angle_success':bool(esol.success)})
 return {'level':'numeric dual design, not certificate','blocks':blocks,'faces':faces,'edges':edges,'weights':alpha.tolist(),'theta_min':theta.tolist(),'history':history,'Q':Q.tolist()}
if __name__=='__main__':
 import sys
 blocks=tuple(map(int,sys.argv[1].split(','))) if len(sys.argv)>1 else(2,3,4)
 out=run(blocks)
 (P/'evidence'/('network-scout-'+''.join(map(str,blocks))+'.json')).write_text(json.dumps(out,indent=2))
 print(json.dumps({'blocks':blocks,'history':out['history']}))
