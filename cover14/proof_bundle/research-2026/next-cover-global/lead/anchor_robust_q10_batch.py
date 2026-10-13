"""29remainingq10, one200step convexrobust-flow design each; deterministic certificate independentofoptimizer success."""
from anchor_robust_flow_probe import solve,P,json
from anchor_simplex_q10_certificate_batch import bound
from anchor_simplex_q10_fraction_replay import replay_record
import time,hashlib
start=time.time();data=json.loads((P/'anchor-simplex-q10-catalogue-probe.json').read_text())['runs'];ret=json.loads((P/'anchor-simplex-q10-retained.json').read_text())['retained'];keep={r['index']for r in ret if r['family']=='10/4'};out=[];cert=[];rep=[]
for row in data:
 if row['index']not in keep:continue
 opt=solve(row,10);out.append(opt);c=bound(opt)
 if c['status']=='excluded_pending_fraction_replay':
  r=replay_record(c);assert r['excluded'];cert.append(c);rep.append(r);print('EXACT',r['index'],r['lower_radius_display'],flush=True)
 (P/'anchor-robust-q10-proposals.json').write_text(json.dumps({'status':'numeric_robust_flow_designs','runs':out},indent=2));cp=P/'anchor-robust-q10-certificates.json';cp.write_text(json.dumps({'status':'directed_global_simplex_bounds','runs':cert},indent=2));(P/'anchor-robust-q10-replays.json').write_text(json.dumps({'status':'independent_fraction_bounds','source_sha256':hashlib.sha256(cp.read_bytes()).hexdigest(),'runs':rep,'seconds':time.time()-start},indent=2))
print('DONE',len(out),'excluded',len(cert),'seconds',time.time()-start,flush=True)
