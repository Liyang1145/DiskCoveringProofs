"""Exact-force/interval full-cell certification near seven simplex corners.
Uses independent postprocessing; solver values never premises.
"""
import json
from fractions import Fraction as F
from pathlib import Path
from simplex_tree_pilot import repair,field,lower,I,lo
P=Path(__file__).resolve().parent
src=json.loads((P.parent/'r20-alternative/corner_force_proposals.json').read_text())['corners']
v2=json.loads((P.parent/'r20-alternative/fixed_oracle_v2.json').read_text())['corners']
replacements={s['corner']:s for s in v2}
src=[replacements.get(s['corner'],s) for s in src]
root=[[F(i==j) for i in range(9)] for j in range(9)]
rows=[]
for s in src:
 j=s['corner']
 if not s.get('success',False):
  rows.append({'corner':j,'status':'proposal_failed_not_used'});continue
 ff=field(repair(s['p_51']),'corner'+str(j))
 # Conv{(1-t)e_j+t e_k}; equivalent y_j>=1-t. Test rational t then recheck selected cell.
 passed=[]
 for n in range(1,21):
  t=F(n,20);verts=[[(1-t)*root[j][i]+t*root[k][i] for i in range(9)] for k in range(9)]
  lb=lower(verts,ff)
  if lb>I(F(19,50)):passed.append((t,lb))
 if not passed:
  rows.append({'corner':j,'status':'no_cell_certified'});continue
 t,_=passed[-1];verts=[[(1-t)*root[j][i]+t*root[k][i] for i in range(9)] for k in range(9)]
 lb=lower(verts,ff);assert lb>I(F(19,50))
 rows.append({'corner':j,'status':'proved-interval','t':str(t),'y_corner_lower':str(1-t),'lower':str(lo(lb)),'forces':[[str(v) for v in q] for q in ff['forces']]})
print([{k:v for k,v in row.items() if k!='forces'} for row in rows])
(P/'corner_simplex_certificates.json').write_text(json.dumps({'scope':'union of listed corner simplexes only, NOT global P','rows':rows,'repro':'py -3 -B research-2026/team-current/lead/certify_corner_simplexes.py'},indent=2))
