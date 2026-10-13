"""Bounded threeq11 jointCartesiangapcontrols; no globalminimumclaim."""
from anchor_outer_local_probe import run,P,json
from q11_chord_polytope import chord_middles
rows=json.loads((P/'anchor-simplex-q11-catalogue-probe.json').read_text())['runs'];out=[]
for idx in [58,510,75]:
 row=next(r for r in rows if r['index']==idx);r=run(row);r['chord_middles']=chord_middles(row['faces']);out.append(r);(P/'q11-outer-controls.json').write_text(json.dumps({'status':'numeric_only_jointlocalcontrols','runs':out},indent=2))
