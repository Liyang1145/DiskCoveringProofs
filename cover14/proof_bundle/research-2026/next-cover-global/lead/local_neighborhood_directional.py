"""Direct congruence-direction interval AD for explicit local exclusion.
Same mathematical penalty as LOCAL-FACTORED-BOX; changes only representation.
"""
import os,json,numpy as np
import local_sosc_certificate as b
from local_sosc_certificate import I,J,Q,S,mid,norm,boundary,circum,P,C,r,lam,g,positive
EPS=Q(os.environ.get('N14_LOCAL_EPS','1/25000'));K=I(Q(os.environ.get('N14_LOCAL_K','3')))
AA=np.array([[mid(b.HL[i][j]+K*sum((b.grads[k][i]*b.grads[k][j]for k in positive),I(0))+K*I(int(i==j==19)))for j in range(28)]for i in range(28)])
WW=np.linalg.inv(np.linalg.cholesky(AA)).T
W=[[I(Q(format(x,'.17g')))for x in row]for row in WW];W=[[I(x.lo,x.lo,True)for x in row]for row in W]
# J's module-global dimension is read by its methods. Base point certificates completed before this change.
b.N=28
CC=[tuple(I(x.lo-I(EPS).hi,x.hi+I(EPS).hi,True)for x in p)for p in C]
H=[[I(0)for j in range(28)]for i in range(28)];minnearest=[];mins=[]
for k in positive:
 entry=(g['anchors']+g['faces'])[k];ids=entry['owners']if k<10 else entry['ids']
 ps=[[J(CC[i][j],g=list(W[2*i+j]))for j in range(2)]for i in ids]
 if k<10:
  pp,qq=[C[i]for i in ids];dv=[qq[j]-pp[j]for j in range(2)];ba=[v*((norm(qq)-norm(pp))/2/norm(dv))for v in dv];anchor=b.anchors[k]
  sg=-dv[1]*(anchor[0]-ba[0])+dv[0]*(anchor[1]-ba[1]);assert sg.lo*sg.hi>0;sign=1 if sg.lo>0 else-1
  f=boundary(*ps,sign)
  p,q=[CC[i]for i in ids];vv=[q[j]-p[j]for j in range(2)];bb=[v*((norm(q)-norm(p))/2/norm(vv))for v in vv];rad=((1-norm(bb))/norm(vv)).sqrt();w=[bb[0]-sign*vv[1]*rad,bb[1]+sign*vv[0]*rad]
 else:
  f=circum(*ps)
  p,q,v=[CC[i]for i in ids];u=[q[j]-p[j]for j in range(2)];vv=[v[j]-p[j]for j in range(2)];dd=u[0]*vv[1]-u[1]*vv[0];aa=(norm(q)-norm(p))/2;bb=(norm(v)-norm(p))/2;w=[(aa*vv[1]-u[1]*bb)/dd,(u[0]*bb-aa*vv[0])/dd];assert (1-norm(w)).lo>0
 for ii in range(14):
  if ii in ids:continue
  sep=norm([w[j]-CC[ii][j]for j in range(2)])-f.v;assert sep.lo>0;minnearest.append(sep.lo)
 delta=f.v-r*r;sgn=2*lam[k]+K*delta;assert sgn.lo>0;mins.append(sgn.lo)
 for i in range(28):
  for j in range(28):H[i][j]+=(lam[k]+K*delta)*f.h[i][j]+K*f.g[i]*f.g[j]
 print('contact',k,'done',flush=True)
for i in range(28):
 for j in range(28):H[i][j]+=K*W[19][i]*W[19][j]
errors=[[max(abs(H[i][j].lo-int(i==j)*S),abs(H[i][j].hi-int(i==j)*S))for j in range(28)]for i in range(28)]
ee=np.array([[x/S for x in row]for row in errors]);vals,vecs=np.linalg.eig(ee);v=np.abs(vecs[:,np.argmax(vals.real)].real);v/=max(v);weights=[Q(format(float(x),'.15g'))for x in v];assert min(weights)>0
bound=max(sum((Q(errors[i][j],S)*weights[j]for j in range(28)),Q(0))/weights[i]for i in range(28));print('exact weighted row bound display',float(bound),flush=True)
out={'status':'certified_explicit_neighborhood_quadratic_control'if bound<1 else 'inconclusive_interval_width','scope':'exactroot-centered gauged28coordinatebox; exactKKTanalyticpremise','epsilon':str(EPS),'penalty':str(os.environ.get('N14_LOCAL_K','3')),'matrix_test':'perron','perron_weights':list(map(str,weights)),'perron_bound':str(bound),'min_penalty_sign_lower':str(Q(min(mins),S)),'min_other_site_squared_separation':str(Q(min(minnearest),S)),'transformed_H_intervals':[[[str(Q(x.lo,S)),str(Q(x.hi,S))]for x in row]for row in H],'W_exact':[[str(Q(x.lo,S))for x in row]for row in W]}
(P/os.environ.get('N14_LOCAL_OUTPUT','local-neighborhood-directional-4e5.json')).write_text(json.dumps(out,indent=2));assert bound<1
