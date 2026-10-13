"""Whole q10 simplex certificate by exact balancedflow and global Taylor lowerquadratic."""
from fixed_anchor_flow_certificate import certify
from area_safe_certificate import I,Q,S,PI,L,U,trig,P
import json
src=json.loads((P/'anchor-simplex-probe.json').read_text())['runs'];row=next(x for x in src if x['case']=='q10-391');flow=certify(row,Q(0));z=[list(map(Q,p))for p in flow['flow_vectors']];q=10;nf=len(row['faces']);assert row['faces']==json.loads((P/'k10-catalogue-corrected.json').read_text())['10/4'][391]['faces'];assert row['owners']==[[j,(j+1)%q]for j in range(q)]
assert (2*PI-9*L).lo>0 and(10*L-2*PI).lo>0
b=[[sum(z[3*nf+2*j+h][k]for h in range(2))for k in range(2)]for j in range(q)];g=[[-x for x in bb]for bb in b];den=I(Q(flow['norm_denominator_upper']));t0=list(map(Q,flow['angle_center_radians']));F0=I(0);grad=[];norms=[]
for t,gg in zip(t0,g):
 sn,cs=trig(I(t));F0+=I(gg[0])*cs+I(gg[1])*sn;grad.append(-I(gg[0])*sn+I(gg[1])*cs);a=sum(x*x for x in gg);norms.append(I(a).sqrt()if a else I(0))
delta=10*L-2*PI;bounds=[]
for vertex in range(q):
 val=F0
 for j in range(q):
  t=j*L-(delta if vertex<j else I(0))
  if t0[j]<0:t-=2*PI
  dt=t-I(t0[j]);val+=grad[j]*dt-norms[j]*dt*dt/2
 bounds.append((val/den).lo)
lo=min(bounds);assert lo>I(U).hi
out={'status':'global_q10_simplex_excluded_pending_independent_replay','family':'10/4','index':391,'lower_radius_exact':str(Q(lo,S)),'lower_radius_display':lo/S,'vertices_lower_exact':[str(Q(v,S))for v in bounds],'flow':flow,'domain':'theta_i in[0,L], sumtheta2pi, L=2asinU; gaugeA0=(1,0); q10 simplex deficits d=L-theta sum10L-2pi','proof':'Taylor lowerquadratic is concave in deficits;minimum attainedatoneofthe10simplexvertices. No sample-to-continuum inference.'};(P/'anchor-simplex-certificate.json').write_text(json.dumps(out,indent=2));print({k:v for k,v in out.items()if k not in ['flow','vertices_lower_exact']})
