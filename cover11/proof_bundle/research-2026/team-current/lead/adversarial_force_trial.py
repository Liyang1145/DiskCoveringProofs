"""One new force at root-game adversarial anchor point. No sweep."""
from multifield_simplex_pilot import *
import sys
sys.path.insert(0,str(P.parent/'r20-alternative'))
from fixed_oracle_v2 import propose_from_widths
report=json.loads((P/'root_game_diagnostic.json').read_text());w=report['widths']
sol=propose_from_widths(w);ff=field(repair(sol['p_51']),'adversarial0')
y=[F(x) for x in report['adversarial_y']]
pointbound=lower([y]*9,ff)
d0=json.loads((P/'multifield_simplex_pilot.json').read_text());fields=[field([[F(x) for x in q] for q in f['forces']],f['name']) for f in d0['fields']]
root=[[F(i==j) for i in range(9)] for j in range(9)];before=game(table(root,fields))[0];fields.append(ff);after=game(table(root,fields))[0]
out={'scope':'single diagnostic point plus rigorous root lower bound, NOT optimum certificate','point_y':[str(x) for x in y],'solver_r':sol['r'],'solver_success':sol['success'],'certified_point_lower':str(lo(pointbound)),'root_game_before':str(before),'root_game_after':str(after),'forces':[[str(x) for x in q] for q in ff['forces']]}
(P/'adversarial_force_trial.json').write_text(json.dumps(out,indent=2));print({k:v for k,v in out.items() if k!='forces'})
