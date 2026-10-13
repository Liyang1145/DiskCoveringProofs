"""Safe coarse area relaxation: boundary caps bounded by chordconvexity, notfalsef(alpha).
Bounded12graphs+knownstarcontrols; numericoptimization NOT rigorousupperbound.
"""
import json,math,numpy as np
from pathlib import Path
from itertools import combinations
from scipy.optimize import minimize
P=Path(__file__).resolve().parent
def solve(n,q,edges,r):
 E=len(edges);L=2*math.asin(r);cap=math.pi*(1-math.sin(L)/L)
 B=np.zeros((n,q+E))
 for i in range(q):B[i,i]=1
 for k,(i,j)in enumerate(edges):B[i,q+k]=1;B[j,q+k]=1
 coeff=np.r_[np.full(q,r*r/2),np.full(E,r*r)]
 def obj(x):return -cap-sum(coeff*np.sin(x)),-coeff*np.cos(x)
 res=minimize(obj,np.full(q+E,2*n*np.pi/(q+2*E)),jac=True,method='SLSQP',bounds=[(0,np.pi)]*(q+E),constraints=[{'type':'eq','fun':lambda x:B@x-2*np.pi,'jac':lambda x:B}],options={'maxiter':400,'ftol':1e-12})
 return {'success':bool(res.success),'minus_pi':float(-res.fun-np.pi),'area':float(-res.fun),'angles':res.x.tolist(),'eqresid':float(max(abs(B@res.x-2*np.pi)))}
if __name__=='__main__':
 D=json.loads((P/'q11-pocket-catalogue.json').read_text());inds=json.loads((P/'q11-double-chord-pruning.json').read_text())['retained_indices'];out=[]
 for idx in inds[:12]:
  e=D['entries'][idx];edges=sorted({tuple(sorted(uv))for f in e['faces']for uv in combinations(f,2)});res=solve(14,11,edges,.33173203427623414);res['index']=idx;out.append(res)
 (P/'area-safe-probe.json').write_text(json.dumps({'status':'numeric_only_safe_coarse_relaxation_draft','runs':out},indent=2));print([(x['index'],x['minus_pi'],x['eqresid'])for x in out])
