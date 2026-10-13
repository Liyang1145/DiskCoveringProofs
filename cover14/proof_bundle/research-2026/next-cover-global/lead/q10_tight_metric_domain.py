"""Intersect independentlyaudited C1331/2domain with C1333 cuts using scalar rational clipping."""
from q10_rational_polytope_audit import *
if __name__=='__main__':
 source=P/'q10-reduced-metric-domain.json';p=json.loads(source.read_text())['polytope'];V,cs=decode(p);cuts=json.loads((P/'q10-slab-transport.json').read_text())['cuts'];hist=[]
 for cut in cuts:
  s=Q(1)if cut['sense']=='greater'else Q(-1);n=tuple(s*int(i in cut['indices'])for i in range(10));r=s*Q(cut['fraction_of_total']);before=len(V);V,_=clip(V,cs,n,r);cs.append((n,r));hist.append({'cut':cut,'before':before,'after':len(V)});print('TIGHTCUT',cut,len(V),flush=True)
 triples=lambda x:[str(10*x),'0',str(-x)];poly={'dim':10,'vertex_set':[[triples(x)for x in v]for v in sorted(V)],'inequalities':[[list(map(str,n)),triples(r),f'constraint{i}']for i,(n,r)in enumerate(cs)],'equality':[['1']*10,['10','0','-1']]};out={'status':'sourcebound_rational_clip_necessary_domain','polytope':poly,'cuts':hist,'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'transport_sha256':hashlib.sha256((P/'q10-slab-transport.json').read_bytes()).hexdigest()};(P/'q10-tight-metric-domain.json').write_text(json.dumps(out,indent=2));print('TIGHTROOT',len(V))
