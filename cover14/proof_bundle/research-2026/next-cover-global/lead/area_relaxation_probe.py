"""Bounded calibration of global area/angle relaxation, NOT interval exclusion.
One known sharp n8/9/10 star control; n14 bestsaved graph; selected q11 representatives.
"""
import numpy as np,json,math
from pathlib import Path
from itertools import combinations
from scipy.optimize import minimize
P=Path(__file__).resolve().parent
def solve(n,q,edges,r):
 E=len(edges);B=np.zeros((n,q+E))
 for i in range(q):B[i,i]=1
 for k,(i,j)in enumerate(edges):B[i,q+k]=1;B[j,q+k]=1
 def funs(x):
  a=x[:q];b=x[q:];h=r*np.sin(a/2);th=2*np.arcsin(h);tp=r*np.cos(a/2)/np.sqrt(1-h*h)
  FF=(th-np.sin(th)+r*r*np.sin(a))/2;Fp=((1-np.cos(th))*tp+r*r*np.cos(a))/2
  area=np.sum(FF)+r*r*np.sum(np.sin(b));grad=np.r_[Fp,r*r*np.cos(b)]
  return area,grad,th,tp
 def obj(x):f,g,_,_=funs(x);return -f,-g
 def cap(x):return sum(funs(x)[2])-2*np.pi
 def capjac(x):return np.r_[funs(x)[3],np.zeros(E)]
 x=np.r_[np.full(q,2*np.arcsin(np.sin(np.pi/q)/r)),np.full(E,(n*np.pi-q*np.arcsin(np.sin(np.pi/q)/r))/E)]
 res=minimize(obj,x,jac=True,method='SLSQP',bounds=[(.000001,np.pi-.000001)]*(q+E),constraints=[{'type':'eq','fun':lambda x:B@x-2*np.pi,'jac':lambda x:B},{'type':'ineq','fun':cap,'jac':capjac}],options={'maxiter':600,'ftol':1e-11})
 return {'n':n,'q':q,'E':E,'r':r,'success':bool(res.success),'message':str(res.message),'max_area_numeric':-res.fun,'minus_pi':-res.fun-np.pi,'equality_residual':float(max(abs(B@res.x-2*np.pi))),'cap_residual':float(cap(res.x)),'angles':res.x.tolist()}
if __name__=='__main__':
 out={'status':'numeric_only','controls':[],'q11_examples':[]}
 for n in(8,9,10):
  q=n-1;edges=sorted({tuple(sorted((i,(i+1)%q)))for i in range(q)}|{(i,q)for i in range(q)})
  out['controls'].append(solve(n,q,edges,1/(1+2*np.cos(2*np.pi/q))))
 # Bestsavedcandidate graph hasinternalTCTslacktrianglesaswell; stresssupportsource14tightfacesomits2slackfaces so add explicitly.
 g=json.loads((P/'stress-barycentric-result.json').read_text());faces=[x['ids']for x in g['faces']]+[[4,6,12],[5,7,13]]
 # remap ringpositions0..9 andhubs10..13 (savedsite ring is0..9 already).
 edges=sorted({tuple(sorted(e))for f in faces for e in combinations(f,2)});assert len(edges)==29
 out['candidate']=solve(14,10,edges,.33173203427623414)
 D=json.loads((P/'q11-pocket-catalogue.json').read_text());inds=json.loads((P/'q11-double-chord-pruning.json').read_text())['retained_indices']
 # Atmost12 distinctdegreeprofiles; nominateonlycontrastcases, notcataloguecertification.
 seen=set()
 for idx in inds:
  en=D['entries'][idx];edges=sorted({tuple(sorted(e))for f in en['faces']for e in combinations(f,2)});deg=[sum(i in e for e in edges)for i in range(14)];profile=(tuple(sorted(deg[:11])),tuple(sorted(deg[11:])))
  if profile in seen:continue
  seen.add(profile);rr=solve(14,11,edges,.33173203427623414);rr['index']=idx;rr['degrees']=deg;out['q11_examples'].append(rr)
  if len(seen)>=12:break
 (P/'area-relaxation-probe.json').write_text(json.dumps(out,indent=2))
 print('controls',[(x['n'],x['success'],x['minus_pi'])for x in out['controls']]);print('candidate',out['candidate']['max_area_numeric']);print('q11',[(x['index'],x['success'],x['minus_pi'])for x in out['q11_examples']])
