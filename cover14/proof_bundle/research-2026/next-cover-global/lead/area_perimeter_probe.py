"""Bounded21 retained q10 cases violating newly proved view-angle capacity.
One SLSQP<=600 iterations each; one exact rational dual certificate each.
"""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
import json,math,numpy as np
from fractions import Fraction as Q
from itertools import combinations
from scipy.optimize import minimize,linprog
from area_safe_certificate import I,S,PI,L,U,cap_minus_pi,trig,P
D=json.loads((P/'k10-catalogue-corrected.json').read_text());saved=[json.loads(x)for x in(P/'area-safe-catalogue.jsonl').read_text().splitlines()];rr=[]
for row in saved:
 if row['family']!='10/4' or row['status']!='inconclusive':continue
 t=np.array([float(Q(x))for x in row['rational_angles']]);Lf=float((L.lo+L.hi)/(2*S))
 if sum(np.minimum(t[:10],Lf))<2*math.pi:rr.append(row)
assert len(rr)==21
out=[]
for row in rr:
 q=10;n=14;idx=row['index'];edges=sorted({tuple(sorted(e))for f in D['10/4'][idx]['faces']for e in combinations(f,2)});m=q+len(edges);B=np.zeros((n,m));B[:q,:q]=np.eye(q)
 for j,(u,v)in enumerate(edges):B[u,q+j]=B[v,q+j]=1
 a=np.r_[np.full(q,float(U*U/2)),np.full(len(edges),float(U*U))]
 eq=np.zeros((n+1,m+q));eq[:n,:m]=B;eq[-1,m:]=1;rhs=np.r_[np.full(n,2*math.pi),2*math.pi]
 ineq=np.zeros((q,m+q));ineq[:,:q]=np.eye(q);ineq[:,m:]=-np.eye(q)
 x0=np.r_[[float(Q(x))for x in row['rational_angles']],np.full(q,2*math.pi/q)]
 res=minimize(lambda x:-float(a@np.sin(x[:m])),x0,jac=lambda x:np.r_[-a*np.cos(x[:m]),np.zeros(q)],constraints=[{'type':'eq','fun':lambda x:eq@x-rhs,'jac':lambda x:eq},{'type':'ineq','fun':lambda x:ineq@x,'jac':lambda x:ineq}],bounds=[(0,math.pi)]*m+[(0,Lf)]*q,method='SLSQP',options={'maxiter':600,'ftol':1e-12})
 t=[max(Q(0),min(Q('3.141592653589'),Q(format(x,'.12f'))))for x in res.x[:m]];g=a*np.cos(np.array(list(map(float,t))))
 # Min 2pi sumy -2pi mu +sumv; v_j>=boxsup((g-B'y)t+mu min(t,L))boundary.
 A=[];b=[]
 for j in range(m):
  for endpoint,mucoef in ([(Lf,Lf),(math.pi,Lf)]if j<q else[(math.pi,0)]):
   z=np.zeros(n+1+m);z[:n]=-endpoint*B[:,j];z[n]=mucoef;z[n+1+j]=-1;A.append(z);b.append(-endpoint*g[j])
 lp=linprog(np.r_[np.full(n,2*math.pi),-2*math.pi,np.ones(m)],A_ub=A,b_ub=b,bounds=[(None,None)]*n+[(0,None)]+[(0,None)]*m,method='highs');assert lp.success
 y=[Q(format(x,'.12f'))for x in lp.x[:n]];mu=max(Q(0),Q(format(lp.x[n],'.12f')))
 bound=cap_minus_pi+2*PI*(sum(y)-mu)
 for j,x in enumerate(t):
  aa=U*U/(2 if j<q else 1);sn,cs=trig(I(x));bound+=I(aa)*(sn-I(x)*cs);potential=y[j]if j<q else sum(y[i]for i in edges[j-q]);slope=I(aa)*cs-potential
  vs=[I(0),PI*slope]
  if j<q:vs=[I(0),L*(slope+mu),PI*slope+L*mu]
  bound+=I(max(v.lo for v in vs),max(v.hi for v in vs),True)
 rec={'family':'10/4','index':idx,'status':'excluded'if bound.hi<0 else'inconclusive','upper_display':bound.hi/S,'upper_exact':str(Q(bound.hi,S)),'rational_angles':list(map(str,t)),'rational_potentials':list(map(str,y)),'rational_mu':str(mu),'numeric_success':bool(res.success),'numeric_eqresid':float(max(abs(eq@res.x-rhs))),'numeric_ineqresid':float(min(ineq@res.x))};out.append(rec);print(idx,rec['status'],rec['upper_display'],'mu',float(mu),flush=True)
(P/'area-perimeter-probe.json').write_text(json.dumps({'status':'exact_supporting_planes','scope':'21 previouslyretainedq10m4 graphs selectedforcapacityviolation; nootherclasseschecked','runs':out},indent=2))
