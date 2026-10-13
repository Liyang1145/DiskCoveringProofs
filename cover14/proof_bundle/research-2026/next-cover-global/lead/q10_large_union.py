"""Union singleleaf uppercap and three completeexterior trees, all sourcebound."""
from q10_rational_polytope_audit import *
if __name__=='__main__':
 single=P/'q10-large-deficit-audit.json';ss=json.loads(single.read_text());assert ss['source_sha256']==hashlib.sha256((P/'q10-large-deficit-controls.json').read_bytes()).hexdigest();cuts={(tuple(c['indices']),c['sense'],c['fraction_of_total'])for c in ss['cuts']};trees=[];autos=json.loads((P/'q10-fan-transport.json').read_text())['runs'];mins=[Q(r['replay']['lower_radius_exact'])for r in ss['runs']]
 for ix in [1,2,3]:
  p=P/f'q10-large-partition-{ix}-audit.json';a=json.loads(p.read_text());assert a['status']=='complete_exterior_exclusion'and not a['open_cells'];assert a['source_sha256']==hashlib.sha256((P/f'q10-large-partition-{ix}.json').read_bytes()).hexdigest();assert a['domain_sha256']==hashlib.sha256((P/'q10-c1341-domain.json').read_bytes()).hexdigest();lo=min(Q(r['lower_exact'])for r in a['excluded_leaves']);assert lo>Q('.33173203427623414');mins.append(lo);trees.append({'index':ix,'audit_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'nodes':a['nodes'],'leaves':len(a['excluded_leaves']),'minimum_lower':str(lo)})
  for g in autos:
   dg={int(k):v for k,v in g['deficit_permutation'].items()};cuts.add((tuple(sorted(dg[i]for i in a['indices'])),'greater'if a['side']==-1 else'less',a['threshold']))
 out={'status':'complete_large_deficit_exterior_union','single_audit_sha256':hashlib.sha256(single.read_bytes()).hexdigest(),'trees':trees,'cuts':[{'indices':list(ids),'sense':s,'fraction_of_total':t}for ids,s,t in sorted(cuts)]};(P/'q10-large-union.json').write_text(json.dumps(out,indent=2));print('LARGEUNION',len(trees),'min',float(min(mins)),out['cuts'])
