"""Bounded combined support probe: exact jointcornerarea + normalizedarc capacity."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
import json,math,numpy as np
from itertools import combinations
from scipy.optimize import linprog,brentq
from scipy.sparse import lil_matrix
from area_safe_certificate import I,Q,S,PI,U,trig,asin,P
from innernorm_combined_probe import verts,lines
r=float(U);An=2*math.asin(r/2);cAn=(An-math.sin(An))/2;A=2*asin(U/2);cA=(A-I(U)*(1-I(U*U)/4).sqrt())/2

def asinz(z):
 # Outward round to20decimalplaces before exactasin, saving huge integerpowers.
 scale=10**20;lo=Q((z.lo*scale)//S,scale);hi=Q(-((-z.hi*scale)//S),scale)
 assert 0<=lo<=hi<1
 return I(asin(lo).lo,asin(hi).hi,True)
def bv(t):return 2*math.asin(r*math.sin(t/2))
def bp(t):return r*math.cos(t/2)/math.sqrt(1-r*r*math.sin(t/2)**2)
def fn(t,nu):
 z=r*math.sin(t/2);return r*r/2*math.cos(t)+(z*z+nu)*bp(t)
def fval(t,nu):
 b=bv(t);return r*r/2*math.sin(t)+(b-math.sin(b))/2+nu*b

def verify(q,edges,angles,y,nu,lam):
 assert nu>=0 and lam>=0 and len(y)==14 and len(angles)==q+len(edges)
 bound=PI*(2*sum(y)-2*nu-2*lam-1)
 for j,x in enumerate(angles[:q]):
  assert 0<=x and I(x).hi<PI.lo
  sn,cs=trig(I(x));sh,ch=trig(I(x)/2);z=I(U)*sh;root=(1-z*z).sqrt();b=I(0)if x==0 else 2*asinz(z);bpv=I(U)*ch/root
  val=I(U*U/2)*sn+(b-2*z*root)/2+nu*b;der=I(U*U/2)*cs+(z*z+nu)*bpv
  vv=[]
  for a,h in verts:
   vv.extend([val-I(x)*der+a*(der-y[j])+lam*h,cA+nu*A-a*y[j]+lam*h])
  bound+=I(max(v.lo for v in vv),max(v.hi for v in vv),True)
 for j,(u,v)in enumerate(edges):
  x=angles[q+j];assert 0<=x and I(x).hi<PI.lo
  sn,cs=trig(I(x));slope=I(U*U)*cs-y[u]-y[v];bound+=I(U*U)*(sn-I(x)*cs)+PI*I(max(0,slope.lo),max(0,slope.hi),True)
 return bound

def solve_cert(q,edges):
 n=14;m=q+len(edges);grid=np.linspace(0,math.pi,81);mrows=q*2*len(grid)+len(edges)*len(grid);mat=lil_matrix((mrows,n+2+m));rhs=np.zeros(mrows);at=0
 for j in range(q):
  for t in grid:
   b=bv(t);h=min(float(a)+float(k)*t for a,k in lines)
   mat[at,j]=-t;mat[at,n]=b;mat[at,n+1]=h;mat[at,n+2+j]=-1;rhs[at]=-fval(t,0);at+=1
   mat[at,j]=-t;mat[at,n]=An;mat[at,n+1]=h;mat[at,n+2+j]=-1;rhs[at]=-cAn;at+=1
 for j,(u,v)in enumerate(edges):
  for t in grid:
   mat[at,u]=-t;mat[at,v]=-t;mat[at,n+2+q+j]=-1;rhs[at]=-r*r*math.sin(t);at+=1
 lp=linprog(np.r_[np.full(n,2*math.pi),-2*math.pi,-2*math.pi,np.ones(m)],A_ub=mat.tocsr(),b_ub=rhs,bounds=[(None,None)]*n+[(0,None)]*2+[(None,None)]*m,method='highs')
 if not lp.success:return {'status':'no_certificate','message':lp.message}
 y=[Q(format(v,'.12f'))for v in lp.x[:n]];nu=max(Q(0),Q(format(lp.x[n],'.12f')));lam=max(Q(0),Q(format(lp.x[n+1],'.12f')));ts=[]
 for j in range(q):
  # Optimize smoothF+lamh−yα branch independentlyoneachpiece; return a supportingtangentatbestpoint.
  pts=[0,float((verts[1][0].lo+verts[1][0].hi)/(2*S)),float((verts[2][0].lo+verts[2][0].hi)/(2*S)),math.pi];cand=list(pts)
  for seg in range(3):
   slope=float(lines[seg][1]);g=lambda t:fn(t,float(nu))+float(lam)*slope-float(y[j]);lo,hi=pts[seg],pts[seg+1]
   if g(lo)>0 and g(hi)<0:cand.append(brentq(g,lo,hi))
  t=max(cand,key=lambda t:fval(t,float(nu))+float(lam)*min(float(a)+float(k)*t for a,k in lines)-float(y[j])*t);ts.append(max(Q(0),min(Q('3.141592653589'),Q(format(t,'.12f')))))
 for u,v in edges:
  pot=float(y[u]+y[v]);t=0 if pot>=r*r else(math.pi if pot<=-r*r else math.acos(pot/(r*r)));ts.append(max(Q(0),min(Q('3.141592653589'),Q(format(t,'.12f')))))
 b=verify(q,edges,ts,y,nu,lam)
 return {'status':'excluded'if b.hi<0 else'inconclusive','upper_display':b.hi/S,'upper_exact':str(Q(b.hi,S)),'rational_angles':list(map(str,ts)),'rational_potentials':list(map(str,y)),'rational_nu':str(nu),'rational_lambda':str(lam),'sampled_lp_value_not_bound':float(lp.fun-math.pi)}

if __name__=='__main__':
 D10=json.loads((P/'k10-catalogue-corrected.json').read_text());D11=json.loads((P/'q11-pocket-catalogue.json').read_text());saved=[json.loads(x)for x in(P/'innernorm-combined-catalogue.jsonl').read_text().splitlines()];out=[]
 G=json.loads((P/'stress-barycentric-result.json').read_text());faces=[x['ids']for x in G['faces']]+[[4,6,12],[5,7,13]];edges=sorted({tuple(sorted(e))for f in faces for e in combinations(f,2)});rec=solve_cert(10,edges);assert rec['status']!='excluded';rec.update(family='candidate',index=-1);out.append(rec);print('candidate',rec['status'],rec.get('upper_display'),flush=True)
 for fam in ['10/4','11/3']:
  rr=sorted([x for x in saved if x['family']==fam and x['status']=='inconclusive'],key=lambda x:x['upper_display'])[:6]
  for row in rr:
   q=int(fam.split('/')[0]);idx=row['index'];faces=D11['entries'][idx]['faces']if q==11 else D10[fam][idx]['faces'];edges=sorted({tuple(sorted(e))for f in faces for e in combinations(f,2)});rec=solve_cert(q,edges);rec.update(family=fam,index=idx);out.append(rec);print(fam,idx,rec['status'],rec.get('upper_display'),flush=True)
 (P/'joint-innernorm-probe.json').write_text(json.dumps({'status':'exact_interval_planes_analytic_interface','scope':'candidateand12survivorgraphs; gridsproposalsonly','runs':out},indent=2))
