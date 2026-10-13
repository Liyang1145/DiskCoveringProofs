"""164retainedonechordgraphs; exactpolytope robustflow proposal+2arithmeticbounds."""
from anchor_robust_flow_probe import solve,P,json,np
from q11_chord_polytope import chord_middles,enumerate_vertices,iv,Q,S,L
from q11_chord_flow_certificate import bound
from q11_chord_flow_fraction_replay import replay
import hashlib,time
start=time.time();rows=json.loads((P/'anchor-simplex-q11-catalogue-probe.json').read_text())['runs'];out=[];cs=[];reps=[]
for row in rows:
 mid=chord_middles(row['faces'])
 if len(mid)!=1:continue
 poly=enumerate_vertices(mid);VV=np.array([[float(iv(tuple(map(Q,v))).lo/S)for v in V]for V in poly['vertices']]);ll=float(L.lo/S);TT=np.arange(11)*ll-np.c_[np.zeros(len(VV)),np.cumsum(VV[:,:-1],axis=1)];r=solve(row,11,'concave',angle_vertices=TT);r['polytope']=poly;out.append(r);c=bound(r)
 if c['status']=='excluded_pending_fraction_replay':
  rr=replay(c);assert rr['excluded'];cs.append(c);reps.append(rr);print('EXACT',rr['index'],rr['lower_radius_display'],flush=True)
 (P/'q11-onechord-flow-proposals.json').write_text(json.dumps({'status':'numeric_robust_flow_designs','runs':out},indent=2));cp=P/'q11-onechord-flow-certificates.json';cp.write_text(json.dumps({'status':'directed_wholepolytope_bounds','runs':cs},indent=2));(P/'q11-onechord-flow-replays.json').write_text(json.dumps({'status':'independent_fraction_bounds_vertexcoverage_separate','source_sha256':hashlib.sha256(cp.read_bytes()).hexdigest(),'runs':reps,'seconds':time.time()-start},indent=2))
print('DONE',len(out),'excluded',len(cs),'seconds',time.time()-start,flush=True)

