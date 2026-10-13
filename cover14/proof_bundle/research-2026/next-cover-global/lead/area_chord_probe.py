"""12-graph bounded probe of valid asymmetric chord affine envelope."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
import json,math,numpy as np
from itertools import combinations
from scipy.optimize import minimize,linprog
from area_safe_certificate import I,Q,S,PI,L,U,asin,trig,P
A=Q(167,500);k=Q(31,250);alpha0=Q(121,50)
sn,cs=trig(I(alpha0)/2);z=I(U)*sn
f=2*I(asin(Q(z.lo,S)).lo,asin(Q(z.hi,S)).hi,True)
fp=I(U)*cs/(1-z*z).sqrt();intercept=f-I(alpha0)*fp
assert (I(A)-2*asin(U/2)).lo>0 and (I(k)-fp).lo>0 and (I(A)-intercept).lo>0
R=2*PI-9*L;sinR,_=trig(R);capminus=-(18*I(U)*(1-I(U)**2).sqrt()+sinR)/2

def solve_cert(n,q,edges,initial=None):
 m=q+len(edges);B=np.zeros((n,m));B[:q,:q]=np.eye(q)
 for j,(u,v)in enumerate(edges):B[u,q+j]=B[v,q+j]=1
 a=np.r_[np.full(q,float(U*U/2)),np.full(len(edges),float(U*U))];K=(2*PI-q*A)/k;Kn=(2*math.pi-q*float(A))/float(k);gauge=np.r_[np.ones(q),np.zeros(len(edges))]
 x0=np.full(m,1.7)if initial is None else np.array(list(map(float,initial)))
 res=minimize(lambda t:-float(a@np.sin(t)),x0,jac=lambda t:-a*np.cos(t),constraints=[{'type':'eq','fun':lambda t:B@t-2*math.pi,'jac':lambda t:B},{'type':'ineq','fun':lambda t:gauge@t-Kn,'jac':lambda t:gauge}],bounds=[(0,math.pi)]*m,method='SLSQP',options={'maxiter':600,'ftol':1e-12})
 t=[max(Q(0),min(Q('3.141592653589'),Q(format(x,'.12f'))))for x in res.x];g=a*np.cos(np.array(list(map(float,t))))
 lp=linprog(np.r_[np.full(n,2*math.pi),-Kn,np.full(m,math.pi)],A_ub=np.c_[-B.T,gauge,-np.eye(m)],b_ub=-g,bounds=[(None,None)]*n+[(0,None)]+[(0,None)]*m,method='highs')
 if not lp.success:return {'status':'no_certificate','numeric_message':res.message,'lp_message':lp.message}
 y=[Q(format(x,'.12f'))for x in lp.x[:n]];mu=max(Q(0),Q(format(lp.x[n],'.12f')));bound=capminus+2*PI*sum(y)-I(mu)*K
 for j,x in enumerate(t):
  aa=U*U/(2 if j<q else 1);sn,cs=trig(I(x));bound+=I(aa)*(sn-I(x)*cs);potential=y[j]if j<q else sum(y[i]for i in edges[j-q]);slope=I(aa)*cs-potential+(mu if j<q else 0);bound+=PI*I(max(0,slope.lo),max(0,slope.hi),True)
 return {'status':'excluded'if bound.hi<0 else'inconclusive','upper_display':bound.hi/S,'upper_exact':str(Q(bound.hi,S)),'rational_angles':list(map(str,t)),'rational_potentials':list(map(str,y)),'rational_mu':str(mu),'numeric_success':bool(res.success),'numeric_eqresid':float(max(abs(B@res.x-2*math.pi))),'numeric_ineqresid':float(gauge@res.x-Kn)}

if __name__=='__main__':
 D10=json.loads((P/'k10-catalogue-corrected.json').read_text());D11=json.loads((P/'q11-pocket-catalogue.json').read_text());saved=[json.loads(x)for x in(P/'area-safe-catalogue.jsonl').read_text().splitlines()];remaining={(x['family'],x['index'])for x in json.loads((P/'area-sharp-cap.json').read_text())['runs']if x['status']=='inconclusive'};rr=[]
 for fam in ['10/3','10/4','11/3']:rr.extend([x for x in saved if x['family']==fam and(fam,x['index'])in remaining][:4])
 out=[]
 for row in rr:
  fam=row['family'];idx=row['index'];q=int(fam.split('/')[0]);n=q+int(fam.split('/')[1]);faces=D11['entries'][idx]['faces']if q==11 else D10[fam][idx]['faces'];edges=sorted({tuple(sorted(e))for f in faces for e in combinations(f,2)});rec=solve_cert(n,q,edges,list(map(Q,row['rational_angles'])));rec.update(family=fam,index=idx);out.append(rec);print(fam,idx,rec['status'],rec.get('upper_display'),flush=True)
 (P/'area-chord-probe.json').write_text(json.dumps({'status':'exact_interval_bounds','scope':'12specifiedretainedgraphs withvalidasymmetricchordaffineconstraint','envelope_constants':{'A':str(A),'k':str(k),'tangent_point':str(alpha0),'A_margin':(I(A)-2*asin(U/2)).dec(),'slope_margin':(I(k)-fp).dec(),'intercept_margin':(I(A)-intercept).dec()},'runs':out},indent=2))
