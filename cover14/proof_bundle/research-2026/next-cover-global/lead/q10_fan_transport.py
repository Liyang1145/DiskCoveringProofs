"""Finite exact graphautomorphism transport of certifiednode1 exclusion; notsymmetryWLOG."""
from pathlib import Path
from fractions import Fraction as Q
import json,hashlib
P=Path(__file__).resolve().parent
if __name__=='__main__':
 match=json.loads((P/'candidate-catalogue-match.json').read_text());maps=next(r for r in match['runs']if r['index']==879)['exact_matches'];maps=[{int(k):v for k,v in m.items()}for m in maps];first=maps[0];inverse={v:k for k,v in first.items()};faces={frozenset(f)for f in json.loads((P/'k10-catalogue-corrected.json').read_text())['10/4'][879]['faces']};runs=[]
 for m in maps:
  perm={i:m[inverse[i]]for i in range(14)};assert {frozenset(perm[i]for i in f)for f in faces}==faces;assert all((perm[(i+1)%10]-perm[i])%10==(perm[1]-perm[0])%10 for i in range(10));assert (perm[1]-perm[0])%10 in [1,9];dg={i:(perm[(i+1)%10]-1)%10 for i in range(10)};runs.append({'site_permutation':perm,'deficit_permutation':dg,'strict_upper_half_total_cut_indices':sorted(dg[i]for i in [0,1,2])})
 src=P/'q10-fan-leaf-audit.json';audit=json.loads(src.read_text());assert audit['status']=='sourcebound_node1_excluded_under_C1331_fancuts';out={'status':'finite_graphautomorphism_transport_checked','source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'runs':runs,'conclusion':'Each listed deficittriple sum is strictly less than (10L−2pi)/2 for everyfeasible879 system at r<=U. Orientationreversal realizedbyreflection; ownergap d_i belongsowner i+1. Noaverage/symmetryWLOG.'};(P/'q10-fan-transport.json').write_text(json.dumps(out,indent=2));print([r['strict_upper_half_total_cut_indices']for r in runs])
