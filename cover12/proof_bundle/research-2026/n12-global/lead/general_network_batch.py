"""Named finite graph experiment. Each scout capped130 iterations. Certificate
uses rational kappa suggested from numeric M then exact checks; failures retained.
CLI: comma-separated ids or 'all'."""
from network_minimax import solve
from network_interval_certificate import verify,F
from pathlib import Path
import json,sys,time,traceback,math
P=Path(__file__).resolve().parents[1]
cat=json.loads((P/'members/nine-topology/graphs.json').read_text())['graphs']
names=sys.argv[1].split(',');chosen=[g for g in cat if (names==['all'] and not g['family'].startswith('T3')) or g['id'] in names]
rows=[]
for g in chosen:
 name=g['id'];start=time.time()
 try:
  out=solve(g['faces'],name)
  kappa=F(max(1,math.ceil(max(0,-out['M_eigen'])*1000)+1),1000)
  cert=verify(out,kappa)
  cert['graph_id']=name
  (P/'evidence'/('network-certified-'+name+'.json')).write_text(json.dumps(cert,indent=2))
  row={'id':name,'status':'certified network','margin_display':float(F(cert['margin_lower'])),'kappa':str(kappa),'seconds':time.time()-start}
 except Exception as e:
  (P/'evidence'/('network-failure-'+name+'.txt')).write_text(traceback.format_exc())
  row={'id':name,'status':'failed verification or run','error':str(e)[:200],'seconds':time.time()-start}
 rows.append(row);print(json.dumps(row),flush=True)
 (P/'evidence'/('general-batch-'+('all' if names==['all'] else '_'.join(names))+'.json')).write_text(json.dumps(rows,indent=2))
