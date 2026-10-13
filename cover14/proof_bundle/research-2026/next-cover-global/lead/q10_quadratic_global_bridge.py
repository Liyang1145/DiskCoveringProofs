"""Exact cap-penalty and currentdomain bridge for largebox quadraticminorant."""
import json,hashlib
from fractions import Fraction as Q
from pathlib import Path
import q11_chord_flow_fraction_replay as fr
P=Path(__file__).resolve().parent;src=P/'q10-quadratic-minorant-certificate.json';a=json.loads(src.read_text());b=json.loads((P/'q10-quadratic-minorant-fraction-audit.json').read_text());assert b['source_sha256']==hashlib.sha256(src.read_bytes()).hexdigest()and Q(b['row_bound'])<1
width=json.loads((P/'q10-current-angle-width.json').read_text());assert width['source_sha256']==hashlib.sha256((P/'q10-c1366-domain.json').read_bytes()).hexdigest();eps=Q(a['epsilon']);kap=Q(a['kappa']);pen=Q(a['penalty']);th=list(map(Q,a['theta0']));assert eps==Q(1,200)and kap==Q(1,100)and pen==3
assert all(-eps<Q(r['delta_lower'])<=Q(r['delta_upper'])<eps for r in width['bounds'])
# Alternative halfspace-dual proof removes final vertex-list completeness from box entry.
dualsrc=P/'q10-halfspace-angle-dual.json';dual=json.loads(dualsrc.read_text());dualreplay=json.loads((P/'q10-halfspace-angle-dual-replay.json').read_text());assert dual['domain_sha256']==width['source_sha256'] and dualreplay['source_sha256']==hashlib.sha256(dualsrc.read_bytes()).hexdigest()
assert len(dualreplay['bounds'])==10 and all(-eps<Q(lo)<=Q(hi)<eps for lo,hi in dualreplay['bounds'])
q=Q('.03374975397719135');gcap=[-q,0,0,0,q,-q,0,0,0,q];ge=sum(max(abs(Q(lo)-v),abs(Q(hi)-v))for (lo,hi),v in zip(b['gradient'],gcap));bs=[fr.L[1]-(th[5]-th[4]+2*fr.pi[0]),fr.L[1]-(th[0]-th[9])];upper=max(Q(0),*bs)
assert q>pen*eps # h(t)=-qt-pen*t²/2>=0 on[-2eps,0]; else smallpositive allowance.
caploss=2*(q*upper+pen*upper*upper/2);loss=-Q(b['f0'][0])+eps*ge+caploss;rad2=2*loss/kap;assert 0<rad2<Q(1,10**6)**2
# Reference candidatecomparison inheriteddirectrootcalculation, sourceunchangedrationalangles.
ref=json.loads((P/'q10-adaptive-local-bridge.json').read_text());assert Q(ref['reference_anchor_error_squared'])<Q(1,10**14)**2
base=json.loads((P/'q10-adaptive-flow-interval.json').read_text());assert a['theta0']==base['theta0']
out=dict(status='exact_global_domain_to_local_bridge',minorant_source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),domain_sha256=width['source_sha256'],epsilon=str(eps),gradient_l1_error=str(ge),cap_t_upper_bounds=list(map(str,bs)),caploss=str(caploss),loss=str(loss),angle_error_squared=str(rad2),angle_error_upper='1/1000000',scope='Everyfull879 14site/16sharedfacewitness/10orderedunitcircleanchor system in C1366 domain at r<=U (includingallcyclicgapcaps<=L), after productiontoliteralcyclicmap andonecommonrotation, lies in2e-6truecandidateanchorcell by supnorm<=Euclideannorm andexactreferencecomparison; invoke C1355, notC1352growthratio. ConditionalonC1366necessarydomain/completeness andC1355localtheorem; no newglobaltopologyreduction.')
(P/'q10-quadratic-global-bridge.json').write_text(json.dumps(out,indent=2));print({k:float(Q(out[k]))for k in['epsilon','gradient_l1_error','caploss','loss','angle_error_squared']})
