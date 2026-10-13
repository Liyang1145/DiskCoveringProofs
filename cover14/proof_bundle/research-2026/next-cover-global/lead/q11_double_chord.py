"""Exact combinatorial application of two-disjoint chord-triple arc-capacity bound.
Input catalogue only; constantcertificate inq11-double-ear-pruning.json.
"""
import json
from itertools import combinations
from pathlib import Path
P=Path(__file__).resolve().parent
D=json.loads((P/'q11-pocket-catalogue.json').read_text());old=json.loads((P/'q11-double-ear-pruning.json').read_text());keep=[];removed=[];hist={};types={}
for idx,e in enumerate(D['entries']):
 edges={tuple(sorted(uv))for f in e['faces']for uv in combinations(f,2)}
 middles=[i for i in range(11)if tuple(sorted(((i-1)%11,(i+1)%11)))in edges]
 assert len(middles)==len(e['chord_middle_representative'])
 triples=[{(i-1)%11,i,(i+1)%11}for i in middles]
 pair=next(((middles[i],middles[j])for i in range(len(triples))for j in range(i+1,len(triples))if not triples[i]&triples[j]),None)
 if pair:removed.append({'index':idx,'disjoint_chord_middles':pair})
 else:
  keep.append(idx)
  assert len(middles)<=2
  if len(middles)==2:assert (middles[1]-middles[0])%11 in(2,9)
 key=str(len(middles));hist.setdefault(key,[0,0]);hist[key][pair is not None]+=1
assert set(keep)<=set(old['retained_indices'])
out={'status':'exact_combinatorial_pruning_given_arc_capacity_lemma','scope':'q11 any two vertex-disjoint chord triples impossible; populatedpockets included','before':len(D['entries']),'retained_count':len(keep),'removed_count':len(removed),'retained_indices':keep,'removed_witnesses':removed,'by_chord_count_retained_removed':hist,'newly_removed_beyond_double_ear':len(old['retained_indices'])-len(keep)}
(P/'q11-double-chord-pruning.json').write_text(json.dumps(out,indent=2));print({k:v for k,v in out.items()if k not in('retained_indices','removed_witnesses')})
