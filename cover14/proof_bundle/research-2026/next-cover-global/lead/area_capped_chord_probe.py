"""Bounded12survivors testjointperimeter θ<=min(Lbar,A+kα)."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
import json,math,numpy as np
from itertools import combinations
from scipy.optimize import minimize,linprog
import area_chord_probe as C
from area_safe_certificate import I,Q,S,PI,L,U,trig,P
A=Q('0.333272257');k=Q('0.123099267');Lb=Q('0.676277969');T=(Lb-A)/k
assert (I(Lb)-L).lo>0 and T>0 and I(T).hi<PI.lo
# tighterenvelopeconstants separatelycertified inarea-chord-tighten.json andFractionreplay.
def solve_cert(n,q,edges,initial):
 m=q+len(edges);B=np.zeros((n,m));B[:q,:q]=np.eye(q)
 for j,(u,v)in enumerate(edges):B[u,q+j]=B[v,q+j]=1
 a=np.r_[np.full(q,float(U*U/2)),np.full(len(edges),float(U*U))];eq=np.zeros((n+1,m+q));eq[:n,:m]=B;eq[-1,m:]=1;rhs=np.full(n+1,2*math.pi)
 ineq=np.zeros((q,m+q));ineq[:,:q]=float(k)*np.eye(q);ineq[:,m:]=-np.eye(q)
 x0=np.r_[list(map(float,initial)),np.full(q,2*math.pi/q)]
 res=minimize(lambda x:-float(a@np.sin(x[:m])),x0,jac=lambda x:np.r_[-a*np.cos(x[:m]),np.zeros(q)],constraints=[{'type':'eq','fun':lambda x:eq@x-rhs,'jac':lambda x:eq},{'type':'ineq','fun':lambda x:ineq@x+float(A),'jac':lambda x:ineq}],bounds=[(0,math.pi)]*m+[(0,float(Lb))]*q,method='SLSQP',options={'maxiter':600,'ftol':1e-12})
 t=[max(Q(0),min(Q('3.141592653589'),Q(format(x,'.12f'))))for x in res.x[:m]];g=a*np.cos(np.array(list(map(float,t))))
 mat=[];rhs=[]
 for j in range(m):
  vertices=[(0,float(A)),(float(T),float(Lb)),(math.pi,float(Lb))]if j<q else[(0,0),(math.pi,0)]
  for endpoint,h in vertices:
   z=np.zeros(n+1+m);z[:n]=-endpoint*B[:,j];z[n]=h;z[n+1+j]=-1;mat.append(z);rhs.append(-endpoint*g[j])
 lp=linprog(np.r_[np.full(n,2*math.pi),-2*math.pi,np.ones(m)],A_ub=mat,b_ub=rhs,bounds=[(None,None)]*n+[(0,None)]+[(None,None)]*m,method='highs')
 if not lp.success:return {'status':'no_certificate','message':lp.message}
 y=[Q(format(v,'.12f'))for v in lp.x[:n]];mu=max(Q(0),Q(format(lp.x[n],'.12f')));bound=C.capminus+2*PI*(sum(y)-mu)
 for j,x in enumerate(t):
  aa=U*U/(2 if j<q else 1);sn,cs=trig(I(x));bound+=I(aa)*(sn-I(x)*cs);potential=y[j]if j<q else sum(y[i]for i in edges[j-q]);slope=I(aa)*cs-potential
  vv=[I(mu*A),I(T)*slope+mu*Lb,PI*slope+mu*Lb]if j<q else[I(0),PI*slope]
  bound+=I(max(v.lo for v in vv),max(v.hi for v in vv),True)
 return {'status':'excluded'if bound.hi<0 else'inconclusive','upper_display':bound.hi/S,'upper_exact':str(Q(bound.hi,S)),'rational_angles':list(map(str,t)),'rational_potentials':list(map(str,y)),'rational_mu':str(mu),'numeric_success':bool(res.success)}
if __name__=='__main__':
 D10=json.loads((P/'k10-catalogue-corrected.json').read_text());D11=json.loads((P/'q11-pocket-catalogue.json').read_text());saved=[json.loads(x)for x in(P/'area-chord-catalogue.jsonl').read_text().splitlines()];out=[]
 for fam in ['10/4','11/3']:
  rr=[x for x in saved if x['family']==fam and x['status']=='inconclusive'];rr=sorted(rr,key=lambda x:x['upper_display'])[:6]
  for row in rr:
   idx=row['index'];q=int(fam.split('/')[0]);faces=D11['entries'][idx]['faces']if q==11 else D10[fam][idx]['faces'];edges=sorted({tuple(sorted(e))for f in faces for e in combinations(f,2)});rec=solve_cert(14,q,edges,list(map(Q,row['rational_angles'])));rec.update(family=fam,index=idx);out.append(rec);print(fam,idx,rec['status'],rec.get('upper_display'),flush=True)
 (P/'area-capped-chord-probe.json').write_text(json.dumps({'status':'exact_interval_planes','scope':'12smallest-gap survivorgraphs','A':str(A),'k':str(k),'Lbar':str(Lb),'runs':out},indent=2))
