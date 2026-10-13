"""General q10 balancedflow / directed Taylorvertex certificates, preserving all proposalrecords."""
from fixed_anchor_flow_certificate import certify
from area_safe_certificate import I,Q,S,PI,L,U,trig,P
import json,time,hashlib

def bound(row):
 assert row['family']=='10/4';idx=row['index'];flow=certify(row,Q(0));z=[list(map(Q,p))for p in flow['flow_vectors']];q=10;nf=len(row['faces']);assert row['faces']==json.loads((P/'k10-catalogue-corrected.json').read_text())['10/4'][idx]['faces'];assert row['owners']==[[j,(j+1)%q]for j in range(q)];assert (2*PI-9*L).lo>0 and(10*L-2*PI).lo>0
 g=[[-sum(z[3*nf+2*j+h][k]for h in range(2))for k in range(2)]for j in range(q)];den=I(Q(flow['norm_denominator_upper']));t0=list(map(Q,flow['angle_center_radians']));F0=I(0);grad=[];norms=[]
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
 lo=min(bounds)
 return {'status':'excluded_pending_fraction_replay'if lo>I(U).hi else'inconclusive','family':'10/4','index':idx,'lower_radius_exact':str(Q(lo,S)),'lower_radius_display':lo/S,'flow':flow,'vertices_lower_exact':[str(Q(v,S))for v in bounds]}
if __name__=='__main__':
 start=time.time();src=P/'anchor-simplex-q10-catalogue-probe.json';rows=json.loads(src.read_text())['runs'];out=[]
 for row in rows:
  if row['global_taylor_vertex_lower_proposal']<=float(U):continue
  rec=bound(row);out.append(rec);print(rec['index'],rec['status'],rec['lower_radius_display'],flush=True)
 (P/'anchor-simplex-q10-certificates.json').write_text(json.dumps({'status':'directed_interval_pending_fraction_replays','proposal_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'proposal_count':len(rows),'runs':out,'seconds':time.time()-start},indent=2));print('DONE',len(out),'seconds',time.time()-start,flush=True)
