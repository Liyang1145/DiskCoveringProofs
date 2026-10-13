"""Exact finite transport and stored-tree structural provenance; not leaf-kernel replay."""
from pathlib import Path
from fractions import Fraction as Q
import json,hashlib
P=Path(__file__).resolve().parent
load=lambda p:json.loads(p.read_text())
hashfile=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
autos=load(P/'q10-fan-transport.json')['runs']
faces={frozenset(f) for f in load(P/'k10-catalogue-corrected.json')['10/4'][879]['faces']}
owners={frozenset((i,(i+1)%10)) for i in range(10)}
for a in autos:
 p={int(k):v for k,v in a['site_permutation'].items()};dg={int(k):v for k,v in a['deficit_permutation'].items()}
 assert set(p)==set(p.values())==set(range(14))
 assert {frozenset(p[i] for i in f) for f in faces}==faces
 assert {frozenset(p[i] for i in f) for f in owners}==owners
 step=(p[1]-p[0])%10;assert step in (1,9)
 assert all((p[(i+1)%10]-p[i])%10==step for i in range(10))
 # gap_i belongs to site i+1; an isometry/reindexing maps the owner arc to p[i+1].
 assert dg=={i:(p[(i+1)%10]-1)%10 for i in range(10)}
 assert set(dg.values())==set(range(10))
rows=[]
for path in sorted(P.glob('q10-metric-round*-audit.json')):
 stem=path.name.removesuffix('-audit.json');cfg=load(P/(stem+'-config.json'));aud=load(path)
 assert hashfile(P/cfg['domain'])==aud['domain_sha256'];cuts=set();closed=[]
 for case in aud['results']:
  ix=cfg['cases'].index(case['case']);src=P/f'{stem}-{ix}.json';raw=load(src)
  assert hashfile(src)==case['source_sha256'] and raw['case']==case['case']
  assert raw['source_sha256']==aud['domain_sha256']
  nodes=raw['nodes'];pending=set(raw['pending']);seen=set();todo=[0];leaves=set()
  while todo:
   k=todo.pop();assert k not in seen;seen.add(k);n=nodes[k];assert n['id']==k
   if k in pending:assert 'status'not in n;continue
   if n['status']=='split':
    assert len(n['children'])==2 and len(set(n['children']))==2;todo+=n['children']
   else:
    assert n['status']=='leaf_bound_coverage_pending';leaves.add(k)
  assert seen==set(range(len(nodes)))
  assert pending=={c['node']for c in case['open_cells']}
  assert leaves=={c['node']for c in case['excluded_leaves']}
  assert all(Q(c['lower_exact'])>Q('.33173203427623414')for c in case['excluded_leaves'])
  if pending:continue
  closed.append(ix);ids,t,sgn=case['case']
  for a in autos:
   dg={int(k):v for k,v in a['deficit_permutation'].items()}
   cuts.add((tuple(sorted(dg[i]for i in ids)),'greater'if sgn==-1 else'less',Q(t)))
 stored={(tuple(c['indices']),c['sense'],Q(c['fraction_of_total']))for c in aud['cuts']}
 assert cuts==stored
 rows.append(dict(audit=path.name,closed_cases=closed,transported_cuts=len(cuts),sha256=hashfile(path)))
out=dict(status='exact_transport_and_stored_tree_provenance_checked',scope='all round2..8 cut lists; leaf bound validity and complete root/clip geometry inherited',automorphisms=len(autos),faces=len(faces),owner_pairs=len(owners),runs=rows)
(P/'q10-cut-transport-provenance.json').write_text(json.dumps(out,indent=2))
print(json.dumps(out,indent=2))
