"""Numerical stress design, finite experiment only. Certificate checked separately."""
from network_scout import *
import sys

def solve(faces,name,blocks=None):
 nf,edges,B=graph(faces);anchor=np.arange(9)*2*np.pi/9
 n=len(edges);last={};count=0
 def fun(alpha):
  nonlocal count,last
  _,_,Q=schur(alpha,B,nf,anchor)
  theta,val,mineig,sol=min_energy(Q)
  actual,sq,_=schur(alpha,B,nf,theta)
  count+=1;last={'radius':float(np.sqrt(val)),'M_eigen':mineig,'theta':theta.tolist()}
  return -actual,-sq
 sol=minimize(fun,np.ones(n)/n,jac=True,method='SLSQP',bounds=[(1e-6,1)]*n,constraints={'type':'eq','fun':lambda x:x.sum()-1,'jac':lambda x:np.ones(n)},options={'ftol':1e-11,'maxiter':130})
 fun(sol.x)
 out={'level':'numeric only nested minimax scout','name':name,'blocks':blocks,'faces':faces,'weights':sol.x.tolist(),'success':bool(sol.success),'message':str(sol.message),'calls':count,**last}
 (P/'evidence'/('network-minimax-'+name+'.json')).write_text(json.dumps(out,indent=2))
 return out
if __name__=='__main__':
 blocks=tuple(map(int,sys.argv[1].split(','))) if len(sys.argv)>1 else (3,3,3)
 out=solve(triangle(blocks),''.join(map(str,blocks)),blocks)
 print(json.dumps({k:v for k,v in out.items() if k not in ['faces','weights','theta']}))
