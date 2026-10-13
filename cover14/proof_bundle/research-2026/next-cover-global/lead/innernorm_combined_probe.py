"""Combined lower concave capacity: min(newinnernormline,oldchordline,Lbar)."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
import json,math,numpy as np
from itertools import combinations
from scipy.optimize import minimize,linprog
from area_safe_certificate import I,Q,S,PI,L,U,trig,P
from innernorm_line_certificate import A,k
from area_chord_probe import capminus
lines=[(A,k),(Q('0.333272257'),Q('0.123099267')),(Q('0.676277969'),Q(0))]
T1=(lines[1][0]-A)/(k-lines[1][1]);T2=(lines[2][0]-lines[1][0])/lines[1][1]
assert 0<T1<T2 and I(T2).hi<PI.lo
verts=[(I(0),I(A)),(I(T1),I(A+k*T1)),(I(T2),I(lines[2][0])),(PI,I(lines[2][0]))]
def solve_cert(q,edges,initial):
 n=14;m=q+len(edges);B=np.zeros((n,m));B[:q,:q]=np.eye(q)
 for j,(u,v)in enumerate(edges):B[u,q+j]=B[v,q+j]=1
 aa=np.r_[np.full(q,float(U*U/2)),np.full(len(edges),float(U*U))];eq=np.zeros((n+1,m+q));eq[:n,:m]=B;eq[-1,m:]=1;rhs=np.full(n+1,2*math.pi);iq=[];ic=[]
 for a,b in lines[:2]:
  z=np.zeros((q,m+q));z[:,:q]=float(b)*np.eye(q);z[:,m:]=-np.eye(q);iq.extend(z);ic.extend([float(a)]*q)
 iq=np.array(iq);ic=np.array(ic);x0=np.r_[list(map(float,initial)),np.full(q,2*math.pi/q)]
 res=minimize(lambda x:-float(aa@np.sin(x[:m])),x0,jac=lambda x:np.r_[-aa*np.cos(x[:m]),np.zeros(q)],constraints=[{'type':'eq','fun':lambda x:eq@x-rhs,'jac':lambda x:eq},{'type':'ineq','fun':lambda x:iq@x+ic,'jac':lambda x:iq}],bounds=[(0,math.pi)]*m+[(0,float(lines[2][0]))]*q,method='SLSQP',options={'maxiter':600,'ftol':1e-12})
 t=[max(Q(0),min(Q('3.141592653589'),Q(format(x,'.12f'))))for x in res.x[:m]];g=aa*np.cos(np.array(list(map(float,t))));mat=[];rhs=[]
 for j in range(m):
  vv=verts if j<q else[(I(0),I(0)),(PI,I(0))]
  for tx,h in vv:
   end=(tx.lo+tx.hi)/(2*S);hv=(h.lo+h.hi)/(2*S);z=np.zeros(n+1+m);z[:n]=-end*B[:,j];z[n]=hv;z[n+1+j]=-1;mat.append(z);rhs.append(-end*g[j])
 lp=linprog(np.r_[np.full(n,2*math.pi),-2*math.pi,np.ones(m)],A_ub=mat,b_ub=rhs,bounds=[(None,None)]*n+[(0,None)]+[(None,None)]*m,method='highs')
 if not lp.success:return {'status':'no_certificate','message':lp.message}
 y=[Q(format(v,'.12f'))for v in lp.x[:n]];mu=max(Q(0),Q(format(lp.x[n],'.12f')));bound=capminus+2*PI*(sum(y)-mu)
 for j,x in enumerate(t):
  a=U*U/(2 if j<q else 1);sn,cs=trig(I(x));bound+=I(a)*(sn-I(x)*cs);potential=y[j]if j<q else sum(y[i]for i in edges[j-q]);slope=I(a)*cs-potential
  vv=[tx*slope+mu*h for tx,h in verts]if j<q else[I(0),PI*slope];bound+=I(max(v.lo for v in vv),max(v.hi for v in vv),True)
 return {'status':'excluded'if bound.hi<0 else'inconclusive','upper_display':bound.hi/S,'upper_exact':str(Q(bound.hi,S)),'rational_angles':list(map(str,t)),'rational_potentials':list(map(str,y)),'rational_mu':str(mu),'numeric_success':bool(res.success)}
if __name__=='__main__':
 D10=json.loads((P/'k10-catalogue-corrected.json').read_text());D11=json.loads((P/'q11-pocket-catalogue.json').read_text());saved=[json.loads(x)for x in(P/'area-capped-chord-catalogue.jsonl').read_text().splitlines()];out=[]
 for fam in ['10/4','11/3']:
  rr=sorted([x for x in saved if x['family']==fam and x['status']=='inconclusive'],key=lambda x:x['upper_display'])[:6]
  for row in rr:
   q=int(fam.split('/')[0]);idx=row['index'];faces=D11['entries'][idx]['faces']if q==11 else D10[fam][idx]['faces'];edges=sorted({tuple(sorted(e))for f in faces for e in combinations(f,2)});rec=solve_cert(q,edges,list(map(Q,row['rational_angles'])));rec.update(family=fam,index=idx);out.append(rec);print(fam,idx,rec['status'],rec.get('upper_display'),flush=True)
 (P/'innernorm-combined-probe.json').write_text(json.dumps({'status':'exact_interval_bounds_conditional_geometry_interface','lines':[[str(a),str(b)]for a,b in lines],'runs':out},indent=2))
