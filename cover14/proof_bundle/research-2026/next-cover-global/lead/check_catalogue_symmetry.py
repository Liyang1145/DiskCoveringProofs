"""Audit true dihedral canonicalization, no geometry assumed."""
from pathlib import Path
import json,time
P=Path(__file__).resolve().parents[1]
cat=json.loads((P/'members/topology/k-catalogue-n14.json').read_text())
# Recompute ALL dihedral transformations from scratch; the original restricted
# reflection set is not a group, so a stored minimum need not stay minimal
# after rotation of a reflected representative.
from itertools import permutations
out={};repaired={}
for group,entries in cat.items():
 N,m=map(int,group.split('/'));uniq={};changed=0
 for j,e in enumerate(entries):
  fs=tuple(sorted(tuple(sorted(f))for f in e['faces']));best=fs
  for perm in permutations(range(m)):
   for sign in(-1,1):
    for shift in range(N):
     key=tuple(sorted(tuple(sorted((shift+sign*v)%N if v<N else N+perm[v-N]for v in f))for f in fs))
     best=min(best,key)
  changed+=best!=fs
  uniq.setdefault(best,[]).append(j)
 out[group]={'old_count':len(entries),'full_dihedral_count':len(uniq),'changed_keys':changed,'duplicate_groups':[v for v in uniq.values()if len(v)>1]}
 repaired[group]=[{'m':m,'faces':[list(f)for f in k],'source_indices':v,'skeleton':entries[v[0]]['skeleton']}for k,v in sorted(uniq.items())]
(P/'lead/catalogue-symmetry-audit.json').write_text(json.dumps(out,indent=2))
(P/'lead/k10-catalogue-corrected.json').write_text(json.dumps(repaired,indent=1))
print(json.dumps({k:{kk:vv for kk,vv in v.items()if kk!='duplicate_groups'}for k,v in out.items()},indent=2))
