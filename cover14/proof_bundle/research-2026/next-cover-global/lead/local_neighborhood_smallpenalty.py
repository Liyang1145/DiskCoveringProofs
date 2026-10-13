"""Explicit centerbox exclusion using convexpenalized necessary-contact function.
ExactrootKKTanalyticidentity fromLOCAL-SOSC-PROOF.md remainsbearing.
"""
import json,os
import local_sosc_certificate as base
from local_sosc_certificate import I,J,Q,S,mid,norm,boundary,circum,P,C,r,lam,g,positive
EPS=Q(os.environ.get('N14_LOCAL_EPS','1/100000000'));K=I(Q(os.environ.get('N14_LOCAL_K','1')))
CC=[tuple(I(x.lo-I(EPS).hi,x.hi+I(EPS).hi,True)for x in p)for p in C]
H=[[I(0)for j in range(28)]for i in range(28)];delta_intervals=[];minnearest=[]
for k in positive:
 entry=(g['anchors']+g['faces'])[k];ids=entry['owners']if k<10 else entry['ids'];nodes=[2*i+j for i in ids for j in range(2)]
 ps=[[J.var(CC[i][j],2*l+j)for j in range(2)]for l,i in enumerate(ids)]
 if k<10:
  # Rootbranchsign previouslycertified; intervaldiscriminantguaranteesitsanalyticcontinuation.
  pp,qq=[C[i]for i in ids];dv=[qq[j]-pp[j]for j in range(2)];ba=[v*((norm(qq)-norm(pp))/2/norm(dv))for v in dv];anchor=base.anchors[k]
  sg=-dv[1]*(anchor[0]-ba[0])+dv[0]*(anchor[1]-ba[1]);assert sg.lo*sg.hi>0;sign=1 if sg.lo>0 else-1
  f=boundary(*ps,sign)
  p,q=[CC[i]for i in ids];vv=[q[j]-p[j]for j in range(2)];bb=[v*((norm(q)-norm(p))/2/norm(vv))for v in vv];rad=((1-norm(bb))/norm(vv)).sqrt();w=[bb[0]-sign*vv[1]*rad,bb[1]+sign*vv[0]*rad]
 else:
  f=circum(*ps)
  p,q,v=[CC[i]for i in ids];u=[q[j]-p[j]for j in range(2)];vv=[v[j]-p[j]for j in range(2)];dd=u[0]*vv[1]-u[1]*vv[0];aa=(norm(q)-norm(p))/2;bb=(norm(v)-norm(p))/2;w=[(aa*vv[1]-u[1]*bb)/dd,(u[0]*bb-aa*vv[0])/dd];assert (1-norm(w)).lo>0
 for ii in range(14):
  if ii in ids:continue
  sep=norm([w[j]-CC[ii][j]for j in range(2)])-f.v;assert sep.lo>0;minnearest.append(sep.lo)
 delta=f.v-r*r;delta_intervals.append(delta)
 # Forfeasiblef<=r², lambda*delta+K/2*delta²<=0 onthisentirebox.
 assert (2*lam[k]+K*delta).lo>0
 for i,ii in enumerate(nodes):
  for j,jj in enumerate(nodes):H[ii][jj]+=(lam[k]+K*delta)*f.h[i][j]+K*f.g[i]*f.g[j]
H[19][19]+=K
# Exact rational congruence proposed from rootmatrix, to avoid elimination wrapping.
import numpy as np
AA=np.array([[mid(base.HL[i][j]+K*sum((base.grads[k][i]*base.grads[k][j]for k in positive),I(0))+K*I(int(i==j==19)))for j in range(28)]for i in range(28)]);W=np.linalg.inv(np.linalg.cholesky(AA)).T
W=[[I(Q(format(x,'.17g')))for x in row]for row in W]
W=[[I(x.lo,x.lo,True)for x in row]for row in W]
HW=[[sum((H[i][k]*W[k][j]for k in range(28)),I(0))for j in range(28)]for i in range(28)]
H=[[sum((W[k][i]*HW[k][j]for k in range(28)),I(0))for j in range(28)]for i in range(28)]
# Congruence positive definite implies W nonsingular automatically (squarematrix).
L=[[I(int(i==j))for j in range(28)]for i in range(28)];diag=[]
for i in range(28):
 dd=H[i][i]-sum((L[i][k]**2*diag[k]for k in range(i)),I(0));assert dd.lo>0,(i,dd.lo/S,dd.hi/S);diag.append(dd)
 for j in range(i+1,28):L[j][i]=(H[j][i]-sum((L[j][k]*L[i][k]*diag[k]for k in range(i)),I(0)))/dd
out={'status':'certified_explicit_neighborhood_quadratic_control','scope':'axisaligned28coordinatebox |C-C*|infty<=epsilon, gaugeyX+=0, nootherconfigurationcoversat<=r*. ExactrootKKTidentityanalyticpremise','epsilon':str(EPS),'penalty':str(os.environ.get('N14_LOCAL_K','1')),'LDL_pivots':[d.dec()for d in diag],'min_pivot_lower_display':min(d.lo/S for d in diag),'min_other_site_squared_separation':str(Q(min(minnearest),S)),'contact_deltas':[d.dec()for d in delta_intervals]}
(P/os.environ.get('N14_LOCAL_OUTPUT','local-neighborhood-smallpenalty.json')).write_text(json.dumps(out,indent=2));print('EXPLICIT NEIGHBORHOOD',EPS,'minpivot',out['min_pivot_lower_display'],flush=True)

