"""Source-bound finite transport of auditedslab exclusions."""
from q10_rational_polytope_audit import P,Q,json,hashlib
if __name__=='__main__':
 src=P/'q10-metric-slab-audit.json';audit=json.loads(src.read_text());assert audit['source_sha256']==hashlib.sha256((P/'q10-metric-slab-controls.json').read_bytes()).hexdigest();autos=json.loads((P/'q10-fan-transport.json').read_text())['runs'];cuts=set()
 for row in audit['runs']:
  if not row['replay']['excluded']:continue
  for g in autos:
   dg={int(k):v for k,v in g['deficit_permutation'].items()};ids=tuple(sorted(dg[i]for i in range(row['prefix'])));cuts.add((ids,-row['side'],row['threshold']))
 out={'status':'transported_sourcebound_necessary_strict_metriccuts','audit_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'cuts':[{'indices':list(ids),'sense':'greater'if s==1 else'less','fraction_of_total':t}for ids,s,t in sorted(cuts)]};(P/'q10-slab-transport.json').write_text(json.dumps(out,indent=2));print(out['cuts'])
