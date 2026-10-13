"""Almostconcavity certification: negative/uncertainanchorcoefficients get exact normpenalty."""
from fixed_anchor_flow_certificate import certify
from area_safe_certificate import I,Q,S,PI,L,U,trig,P
import json
row=next(r for r in json.loads((P/'anchor-concave-controls.json').read_text())['runs']if r['case']=='q10-843');flow=certify(row,Q(0));z=[list(map(Q,p))for p in flow['flow_vectors']];q=10;nf=len(row['faces']);g=[[-sum(z[3*nf+2*j+h][k]for h in range(2))for k in range(2)]for j in range(q)];den=I(Q(flow['norm_denominator_upper']));t0=list(map(Q,flow['angle_center_radians']));delta=10*L-2*PI;assert delta.hi<PI.lo;eta=[];endpoint=[]
def at(t,gg):
 sn,cs=trig(t);return I(gg[0])*cs+I(gg[1])*sn
for j,gg in enumerate(g):
 lo=j*L-(delta if j>0 else I(0));hi=j*L
 if t0[j]<0:lo-=2*PI;hi-=2*PI
 vals=[at(t,gg)for t in [lo,hi]];positive=all(v.lo>=0 for v in vals);a=sum(x*x for x in gg);eta.append(I(0)if positive or not a else I(a).sqrt());endpoint.append({'j':j,'sign_certified':positive,'penalty_upper':str(Q(eta[-1].hi,S))})
bounds=[]
for vertex in range(q):
 val=I(0)
 for j,gg in enumerate(g):
  t=j*L-(delta if vertex<j else I(0))
  if t0[j]<0:t-=2*PI
  val+=at(t,gg)-eta[j]*(t-I(t0[j]))**2/2
 bounds.append((val/den).lo)
lo=min(bounds);assert lo>I(U).hi;out={'status':'almostconcave_vertex_global_domain_exclusion','family':'10/4','index':843,'flow':flow,'endpoint_sign_checks':endpoint,'lower_radius_exact':str(Q(lo,S)),'lower_radius_display':lo/S,'proof':'phi endpointsnonnegative andwidth<pi implyphi>=0oninterval;otherwise Hessianupper<=norm. F−sumeta(t−t0)^2/2 concave, soF>=minimumvertexvalueofthiscorrectedfunction.'};(P/'anchor-concave-certificate.json').write_text(json.dumps(out,indent=2));print(out['lower_radius_display'],endpoint)
