"""Bounded structural test of missing all-tight circumradius compatibility on saved angles."""
import json,math
from itertools import combinations
from fractions import Fraction as Q
from pathlib import Path
P=Path(__file__).resolve().parent
D10=json.loads((P/'k10-catalogue-corrected.json').read_text());D11=json.loads((P/'q11-pocket-catalogue.json').read_text());rows=[json.loads(x)for x in(P/'joint-innernorm-catalogue.jsonl').read_text().splitlines()];out=[]
for fam in ['10/4','11/3']:
 rr=sorted([x for x in rows if x['family']==fam and x['status']=='inconclusive'],key=lambda x:x['upper_display'])[:6]
 for row in rr:
  q=int(fam.split('/')[0]);idx=row['index'];faces=D11['entries'][idx]['faces']if q==11 else D10[fam][idx]['faces'];edges=sorted({tuple(sorted(e))for f in faces for e in combinations(f,2)});t=list(map(float,map(Q,row['rational_angles'])));B={e:t[q+j]for j,e in enumerate(edges)};count={e:sum(all(v in f for v in e)for f in faces)for e in edges};res=[]
  for j,f in enumerate(faces):
   ee=[tuple(sorted(e))for e in combinations(f,2)]
   if not all(count[e]==2 for e in ee):continue
   bb=[B[e]for e in ee];res.append({'face':j,'angle_sum_defect':sum(bb)-math.pi,'min_beta':min(bb),'max_beta':max(bb)})
  out.append({'family':fam,'index':idx,'upper_bound':row['upper_display'],'interior_faces':res});print(fam,idx,'faces',len(res),'maxdefect',max([abs(x['angle_sum_defect'])for x in res]or[0]),flush=True)
(P/'radius-saturation-probe.json').write_text(json.dumps({'status':'numeric_proposal_diagnostic_only','scope':'12jointdualproposals; tangentanglesnotassertedprimalfeasible','runs':out},indent=2))
