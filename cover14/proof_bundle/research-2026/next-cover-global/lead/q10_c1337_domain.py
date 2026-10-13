"""Integrate C1337 while preserving every prior immutable domain artifact."""
from q10_rational_polytope_audit import *
if __name__=='__main__':
 source=P/'q10-c1334-domain.json';p=json.loads(source.read_text())['polytope'];V,cs=decode(p);cutfile=P/'q10-c1334-slab-audit.json';audit=json.loads(cutfile.read_text());assert audit['base_sha256']==hashlib.sha256(source.read_bytes()).hexdigest();cuts=audit['cuts'];hist=[]
 for cut in cuts:
  s=Q(1)if cut['sense']=='greater'else Q(-1);n=tuple(s*int(i in cut['indices'])for i in range(10));r=s*Q(cut['fraction_of_total']);before=len(V);V,_=clip(V,cs,n,r);cs.append((n,r));hist.append({'cut':cut,'before':before,'after':len(V)});print('C1337CUT',cut,len(V),flush=True)
 triples=lambda x:[str(10*x),'0',str(-x)];poly={'dim':10,'vertex_set':[[triples(x)for x in v]for v in sorted(V)],'inequalities':[[list(map(str,n)),triples(r),f'constraint{i}']for i,(n,r)in enumerate(cs)],'equality':[['1']*10,['10','0','-1']]};out={'status':'sourcebound_rational_clip_necessary_domain_C1337','polytope':poly,'cuts':hist,'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'audit_sha256':hashlib.sha256(cutfile.read_bytes()).hexdigest()};(P/'q10-c1337-domain.json').write_text(json.dumps(out,indent=2));print('C1337ROOT',len(V))

