"""Bounded joint boundaryarea/perimeter support: sampled LP only proposes; concave tangents certify."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
import json,math,numpy as np
from itertools import combinations
from scipy.optimize import linprog,brentq
from scipy.sparse import lil_matrix
from area_safe_certificate import I,Q,S,PI,L,U,trig,asin,P
r=float(U);ln=2*math.asin(r);gamman=(ln-math.sin(ln))/(2*ln);An=2*math.asin(r/2)
gamma=(L-2*I(U)*(1-I(U)**2).sqrt())/(2*L);A=2*asin(U/2)
def bv(t):return 2*math.asin(r*math.sin(t/2))
def bp(t):return r*math.cos(t/2)/math.sqrt(1-r*r*math.sin(t/2)**2)
def solve_cert(q,edges):
 n=14;m=q+len(edges);grid=np.linspace(0,math.pi,81);mrows=q*(len(grid)+2)+len(edges)*len(grid);mat=lil_matrix((mrows,n+1+m));rhs=np.zeros(mrows);at=0
 for j in range(q):
  for t in grid:
   b=bv(t);mat[at,j]=-t;mat[at,n]=b;mat[at,n+1+j]=-1;rhs[at]=-r*r/2*math.sin(t)-gamman*b;at+=1
  for t in [0,math.pi]:
   mat[at,j]=-t;mat[at,n]=An;mat[at,n+1+j]=-1;rhs[at]=-gamman*An;at+=1
 for j,(u,v)in enumerate(edges):
  for t in grid:
   mat[at,u]=-t;mat[at,v]=-t;mat[at,n+1+q+j]=-1;rhs[at]=-r*r*math.sin(t);at+=1
 lp=linprog(np.r_[np.full(n,2*math.pi),-2*math.pi,np.ones(m)],A_ub=mat.tocsr(),b_ub=rhs,bounds=[(None,None)]*n+[(0,None)]+[(None,None)]*m,method='highs')
 if not lp.success:return {'status':'no_certificate','message':lp.message}
 y=[Q(format(v,'.12f'))for v in lp.x[:n]];mu=max(Q(0),Q(format(lp.x[n],'.12f')));nu=I(mu)+gamma;nuf=float(mu)+gamman;bound=PI*(2*sum(y)-2*mu-1);tang=[]
 def gett(fn,pot):
  if fn(0)<=pot:return Q(0)
  if fn(math.pi)>=pot:return Q('3.141592653589')
  return Q(format(brentq(lambda t:fn(t)-pot,0,math.pi),'.12f'))
 for j in range(q):
  t=gett(lambda t:r*r/2*math.cos(t)+nuf*bp(t),float(y[j]));tang.append(str(t));sn,cs=trig(I(t));sh,ch=trig(I(t)/2);z=I(U)*sh
  # t>=0; tiny negative Taylor error atzero may pass asin endpoints; enclosure formula remains signed? handleexactzero.
  if t==0:b=I(0)
  else:b=2*I(asin(Q(z.lo,S)).lo,asin(Q(z.hi,S)).hi,True)
  der=I(U*U/2)*cs+nu*I(U)*ch/(1-z*z).sqrt();val=I(U*U/2)*sn+nu*b;slope=der-y[j];v1=val-I(t)*der+PI*I(max(0,slope.lo),max(0,slope.hi),True);c=nu*A;v2=c-PI*y[j];bound+=I(max(v1.lo,c.lo,v2.lo),max(v1.hi,c.hi,v2.hi),True)
 for u,v in edges:
  pot=y[u]+y[v];t=gett(lambda t:r*r*math.cos(t),float(pot));tang.append(str(t));sn,cs=trig(I(t));slope=I(U*U)*cs-pot;bound+=I(U*U)*(sn-I(t)*cs)+PI*I(max(0,slope.lo),max(0,slope.hi),True)
 return {'status':'excluded'if bound.hi<0 else'inconclusive','upper_display':bound.hi/S,'upper_exact':str(Q(bound.hi,S)),'rational_angles':tang,'rational_potentials':list(map(str,y)),'rational_mu':str(mu),'sampled_lp_value_not_bound':float(lp.fun-math.pi)}
if __name__=='__main__':
 D10=json.loads((P/'k10-catalogue-corrected.json').read_text());D11=json.loads((P/'q11-pocket-catalogue.json').read_text());saved=[json.loads(x)for x in(P/'innernorm-combined-catalogue.jsonl').read_text().splitlines()];out=[]
 G=json.loads((P/'stress-barycentric-result.json').read_text());faces=[x['ids']for x in G['faces']]+[[4,6,12],[5,7,13]];edges=sorted({tuple(sorted(e))for f in faces for e in combinations(f,2)});rec=solve_cert(10,edges);assert rec['status']!='excluded';rec.update(family='candidate',index=-1);out.append(rec);print('candidate',rec['status'],rec.get('upper_display'),flush=True)
 for fam in ['10/4','11/3']:
  rr=sorted([x for x in saved if x['family']==fam and x['status']=='inconclusive'],key=lambda x:x['upper_display'])[:6]
  for row in rr:
   q=int(fam.split('/')[0]);idx=row['index'];faces=D11['entries'][idx]['faces']if q==11 else D10[fam][idx]['faces'];edges=sorted({tuple(sorted(e))for f in faces for e in combinations(f,2)});rec=solve_cert(q,edges);rec.update(family=fam,index=idx);out.append(rec);print(fam,idx,rec['status'],rec.get('upper_display'),flush=True)
 (P/'joint-boundary-probe.json').write_text(json.dumps({'status':'exact_interval_planes_analytic_interface_draft','scope':'candidateand12survivorgraphs; gridsproposalsonly','runs':out},indent=2))
