"""Bounded numerical attack on coarse conditional LP proposal. No intervalclaims."""
from pathlib import Path
import json,math
from scipy.optimize import minimize_scalar
P=Path(__file__).parent;s=(P/'sector_degenerate_probe.py').read_text();marker='\nrows=[]';assert s.count(marker)==1;s=s.split(marker)[0].replace('q0_closure_dual_0_4.json','middle_sector_inward_dual_proposal.json');ns={'__file__':str(P/'sector_degenerate_probe.py')};exec(s,ns)
z=ns['z'];pi=math.pi;R=.38;i=2
# exact degeneratefacet expression, evaluatednumerically
fun=lambda t:(2*math.asin(R*t)-math.sin(2*math.asin(R*t)))/2-z[i]*pi-(z[32+2*i]+z[33+2*i])*t*t-(z[94+2*i]+z[95+2*i])*t+(z[71]+(z[112+(i-1)%9]+z[112+i])/2)*2*math.asin(R*t)
s=minimize_scalar(lambda t:-fun(t),bounds=(75/76,1),method='bounded');corner=max(fun(75/76),fun(1),-s.fun)
rr=json.loads((P/'middle_sector_inward_continuum_probe.json').read_text())['rows'];total=float(ns['const']+sum(ns['vals'])+corner+sum(row['value'] for row in rr if row['sector']!=2))
out={'scope':'numericattack onfiniteLPcandidate, not rigorousupper','numeric_total':total,'pi':pi,'corner2':float(corner),'face_switch_maxima':ns['vals'],'ring_optimized':rr};(P/'middle_inward_proposal_continuum_control.json').write_text(json.dumps(out,indent=2));print(total,pi)
