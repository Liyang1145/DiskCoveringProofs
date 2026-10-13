"""Trace final halfspaces to root and exact source-bound cut insertions; no clipping rerun."""
from pathlib import Path
from fractions import Fraction as Q
import hashlib,json
P=Path(__file__).resolve().parent
files=list(P.glob('q10-*.json'));index={hashlib.sha256(p.read_bytes()).hexdigest():p for p in files}
load=lambda p:json.loads(p.read_text())
scalar=lambda a: Q(a[0])/10 if Q(a[1])==0 and Q(a[0])==-10*Q(a[2]) else (_ for _ in ()).throw(ValueError())
def rows(poly):return [(tuple(map(Q,n)),scalar(r))for n,r,_ in poly['inequalities']]
p=P/'q10-c1366-domain.json';out=[]
while True:
 a=load(p)
 if not a.get('status','').startswith('sourcebound_rational_clip_necessary_domain') or 'audit_sha256' not in a:break
 src=index[a['source_sha256']];audit=index[a['audit_sha256']];b=load(src);cuts=load(audit)['cuts'];assert [h['cut']for h in a['cuts']]==cuts
 expected=rows(b['polytope'])
 for c in cuts:
  sign=1 if c['sense']=='greater' else -1
  assert c['sense'] in ('greater','less')
  expected.append((tuple(Q(sign*int(i in c['indices']))for i in range(10)),sign*Q(c['fraction_of_total'])))
 assert rows(a['polytope'])==expected
 assert a['polytope']['equality']==b['polytope']['equality']
 out.append(dict(domain=p.name,parent=src.name,audit=audit.name,added=len(cuts)))
 p=src
result=dict(status='exact_halfspace_insertion_chain_checked',scope='row necessity inheritance; root/cut proofs and prior vertex completeness inherited',runs=out,earlier_root=p.name,earlier_root_status=load(p).get('status'))
(P/'q10-domain-row-provenance.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
