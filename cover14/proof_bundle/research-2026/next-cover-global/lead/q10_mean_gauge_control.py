"""Bounded same-cell mean-angle-gauge comparison. Shared Fraction arithmetic disclosed."""
from q10_metric_round import load
from q10_reduced_metric_domain import *
from fixed_anchor_flow_certificate import certify
import q11_chord_flow_fraction_replay as fr
from pathlib import Path
import hashlib

def gauge_replay(rec,mean=True):
 # Rebuild incidence and EXACT balance using existing audited replay. Its old-gauge
 # scalar output is unused in mean mode, but its incidence/balance assertions BEAR proof.
 assert rec.get('gauge')=='mean_prefix' if mean else 'gauge'not in rec
 old=fr.replay(rec)
 flow=rec['flow'];z=[list(map(Q,p)) for p in flow['flow_vectors']];nf=len(flow['faces']);g=[[-sum(z[3*nf+2*j+h][k]for h in range(2))for k in range(2)]for j in range(10)];den=sum((fr.normup(v)for v in z),Q(0));t0=list(map(Q,flow['angle_center_radians']));TT=[]
 for V in rec['polytope']['vertices']:
  dd=[fr.iv(tuple(map(Q,v)))for v in V];ss=[fr.point(Q(0))]
  for d in dd[:-1]:ss.append(fr.add(ss[-1],d))
  m=fr.point(Q(0))
  if mean:
   for s in ss:m=fr.add(m,fr.mul(fr.point(Q(1,10)),s))
  ts=[]
  for j in range(10):
   t=fr.add(fr.sub(fr.mul(fr.point(Q(j)),fr.L),ss[j]),m)
   if t0[j]<0:t=fr.sub(t,fr.mul(fr.point(Q(2)),fr.pi))
   ts.append(t)
  TT.append(ts)
 eta=[]
 for j,gg in enumerate(g):
  lo=min(t[j][0]for t in TT);hi=max(t[j][1]for t in TT);assert hi-lo<fr.pi[0];positive=fr.at(fr.point(lo),gg)[0]>=0 and fr.at(fr.point(hi),gg)[0]>=0;eta.append(Q(0)if positive else fr.normup(gg))
 vals=[]
 for tt in TT:
  v=fr.point(Q(0))
  for j,t in enumerate(tt):
   dt=fr.sub(t,fr.point(t0[j]));v=fr.add(v,fr.sub(fr.at(t,g[j]),fr.mul(fr.point(eta[j]/2),fr.mul(dt,dt))))
  vals.append(v[0]/den)
 low=min(vals);low=Q(low.numerator*fr.S//low.denominator,fr.S)
 if not mean:assert str(low)==old['lower_radius_exact']
 return dict(gauge='mean_prefix'if mean else'anchor0',lower_exact=str(low),lower_display=float(low),excluded=low>fr.U,vertices=len(TT),all_positive=all(e==0 for e in eta))

if __name__=='__main__':
 import sys
 src=P/(sys.argv[1]if len(sys.argv)>1 else'q10-metric-round3-2.json');node=int(sys.argv[2])if len(sys.argv)>2 else 0;dest=P/(sys.argv[3]if len(sys.argv)>3 else'q10-mean-gauge-control.json');a=json.loads(src.read_text());n=a['nodes'][node];old=bound(n['flow_proposal'],{'vertices':n['polytope']['vertex_set']});cal=gauge_replay(old,False)
 poly=load(n['polytope']);TT=angles(poly)
 # theta=jL-prefix => m=mean(jL-theta), evaluated only for proposals.
 from q10_polytope_partition_probe import L,S
 TT+=np.mean(np.arange(10)*float(L.lo/S)-TT,axis=1)[:,None]
 row=n['flow_proposal'];AA=np.c_[np.cos(TT.mean(axis=0)),np.sin(TT.mean(axis=0))];D=np.array(row['incidence_matrix']);nf=len(row['faces']);X=np.linalg.lstsq(D,np.vstack([np.zeros((3*nf,2)),np.repeat(AA,2,axis=0)]),rcond=None)[0]
 r=solve_case(row['case'],X[:14],AA,row['faces'],row['owners'],X[14:]);r.update(index=879,family='10/4');r=smooth(r,TT)
 c=dict(index=879,flow=certify(r,Q(0)),polytope={'vertices':poly.to_dict()['vertex_set']},gauge='mean_prefix');new=gauge_replay(c)
 out=dict(status='samecell_gauge_control_no_new_coverage_claim',source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),node=node,old=cal,new=new,certificate=c)
 dest.write_text(json.dumps(out,indent=2));print('GAUGE',cal,new,flush=True)
