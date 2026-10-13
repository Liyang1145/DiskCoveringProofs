"""Sourcebind three complete small exterior trees and transport necessarycuts."""
from q10_rational_polytope_audit import *
if __name__=='__main__':
 cuts=set();trees=[];autos=json.loads((P/'q10-fan-transport.json').read_text())['runs'];mins=[]
 for ix in range(3):
  p=P/f'q10-exterior-partition-{ix}-audit.json';a=json.loads(p.read_text());assert a['status']=='complete_exterior_exclusion' and not a['open_cells'];assert a['source_sha256']==hashlib.sha256((P/f'q10-exterior-partition-{ix}.json').read_bytes()).hexdigest();assert a['domain_sha256']==hashlib.sha256((P/'q10-c1337-domain.json').read_bytes()).hexdigest();lo=min(Q(r['lower_exact'])for r in a['excluded_leaves']);assert lo>Q('.33173203427623414');mins.append(lo);trees.append({'index':ix,'audit_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'nodes':a['nodes'],'leaves':len(a['excluded_leaves']),'minimum_lower':str(lo)})
  for g in autos:
   dg={int(k):v for k,v in g['deficit_permutation'].items()};cuts.add((tuple(sorted(dg[i]for i in a['indices'])),-a['side'],a['threshold']))
 out={'status':'complete_exterior_union_necessarycuts_only','trees':trees,'cuts':[{'indices':list(ids),'sense':'greater'if s==1 else'less','fraction_of_total':t}for ids,s,t in sorted(cuts)]};(P/'q10-exterior-union.json').write_text(json.dumps(out,indent=2));print('EXTERIORUNION',len(trees),'min',float(min(mins)),out['cuts'])
