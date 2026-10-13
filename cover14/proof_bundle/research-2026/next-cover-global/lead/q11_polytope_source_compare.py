"""Map independently enumerated OWNERdeficits to GAPdeficits for every certified chordpattern."""
from pathlib import Path
from fractions import Fraction as F
import json,hashlib
P=Path(__file__).resolve().parent;src=P.parent/'members/dirichlet-cut-audit-cc2/q11-polytope-independent.json';a=json.loads(src.read_text());assert not a['undecided_signs']and all(x['holds']for x in a['certified_chains']);cp=P/'q11-twochord-flow-certificates.json';rows=json.loads(cp.read_text())['runs'];out=[]
for rec in rows:
 poly=rec['polytope'];m=poly['middles_owner'];assert len(m)==2;case=a['cases']['two_chords_middles1_3'];assert case['routes_agree_exactly']and case['all_vertices_feasible']and case['all_active_sets_full_rank'];shift=next(s for s in range(11)if sorted([(1+s)%11,(3+s)%11])==sorted(m));VV=[]
 for v in case['vertices_owner_indexed_triples']:
  gap=[None]*11
  for j,t in enumerate(v):gap[(j+shift-1)%11]=tuple(map(F,t))
  VV.append(tuple(gap))
 target={tuple(tuple(map(F,t))for t in v)for v in poly['vertices']};assert set(VV)==target;out.append({'index':rec['index'],'middles_owner':m,'owner_rotation':shift,'gap_shift_minus_one':True,'exact_vertex_sets_equal':True})
result={'status':'exact_independent_vertexsets_all43_patterns','sources':{str(p.relative_to(P.parent)):hashlib.sha256(p.read_bytes()).hexdigest()for p in [src,cp]},'runs':out};(P/'q11-polytope-source-compare.json').write_text(json.dumps(result,indent=2));print('compared',len(out))
