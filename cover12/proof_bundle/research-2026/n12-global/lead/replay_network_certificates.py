"""Pure verification from saved rational proposed certificates. No numpy/scipy,
no numerical optimizer, and no double input in load-bearing arithmetic."""
from network_interval_certificate import verify,F,P
import json,hashlib,time
paths=[P/'evidence'/f'network-certified-{n}.json' for n in ['117','126','135','144','225','234']]
cat=json.loads((P/'members/nine-topology/graphs.json').read_text())['graphs']
paths += [P/'evidence'/('network-certified-'+g['id']+'.json') for g in cat if not g['family'].startswith('T3')]
assert len(paths)==55
rows=[];start=time.time()
for path in paths:
 data=json.loads(path.read_text());out=verify(data,F(data['kappa']))
 assert out['margin_lower']==data['margin_lower']
 rows.append({'path':str(path.relative_to(P)),'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'margin_lower':out['margin_lower']})
(P/'evidence'/'network-certificates-replay.json').write_text(json.dumps({'status':'certified networks only','count':len(rows),'certificates':rows},indent=2))
print(json.dumps({'verified_networks':len(rows),'seconds':time.time()-start,'minimum_margin_display':min(float(F(v['margin_lower'])) for v in rows)}))
