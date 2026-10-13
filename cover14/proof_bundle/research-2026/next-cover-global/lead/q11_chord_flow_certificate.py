"""Directed concavity/curvaturepenalty bounds on completeq11chordpolytope."""
from fixed_anchor_flow_certificate import certify
from q11_chord_polytope import *
from area_safe_certificate import trig

def bound(row,domain=None):
 q=len(row['owners']);idx=row['index']
 if domain is None:
  assert q==11;mid=chord_middles(row['faces']);poly=enumerate_vertices(mid);assert poly==row['polytope']
 else:poly=domain
 source=json.loads((P/('q11-pocket-catalogue.json'if q==11 else'k10-catalogue-corrected.json')).read_text());faces=source['entries'if q==11 else'10/4'][idx]['faces'];assert row['faces']==faces;assert row['owners']==[[j,(j+1)%q]for j in range(q)]
 flow=certify(row,Q(0));z=[list(map(Q,p))for p in flow['flow_vectors']];nf=len(row['faces']);g=[[-sum(z[3*nf+2*j+h][k]for h in range(2))for k in range(2)]for j in range(q)];den=I(Q(flow['norm_denominator_upper']));t0=list(map(Q,flow['angle_center_radians']));TT=[]
 for V in poly['vertices']:
  dd=[iv(tuple(map(Q,v)))for v in V];ts=[]
  for j in range(q):
   t=j*L-sum(dd[:j],I(0))
   if t0[j]<0:t-=2*PI
   ts.append(t)
  TT.append(ts)
 def at(t,gg):
  sn,cs=trig(t);return I(gg[0])*cs+I(gg[1])*sn
 eta=[];checks=[]
 for j,gg in enumerate(g):
  lo=I(min(t[j].lo for t in TT),min(t[j].lo for t in TT),True);hi=I(max(t[j].hi for t in TT),max(t[j].hi for t in TT),True);assert hi.hi-lo.lo<PI.lo;positive=at(lo,gg).lo>=0 and at(hi,gg).lo>=0;a=sum(x*x for x in gg);eta.append(I(0)if positive or not a else I(a).sqrt());checks.append(positive)
 lower=[]
 for tt in TT:
  val=I(0)
  for j,t in enumerate(tt):val+=at(t,g[j])-eta[j]*(t-I(t0[j]))**2/2
  lower.append((val/den).lo)
 lo=min(lower);return {'status':'excluded_pending_fraction_replay'if lo>I(U).hi else'inconclusive','family':'11/3'if q==11 else'10/4','index':idx,'lower_radius_exact':str(Q(lo,S)),'lower_radius_display':lo/S,'flow':flow,'polytope':poly,'endpoint_signs':checks}
if __name__=='__main__':
 rows=json.loads((P/'q11-chord-flow-controls.json').read_text())['runs'];out=[]
 for row in rows:
  rec=bound(row);out.append(rec);print(rec['index'],rec['status'],rec['lower_radius_display'],flush=True)
 (P/'q11-chord-flow-control-certificates.json').write_text(json.dumps({'status':'directed_interval_controls','runs':out},indent=2))
