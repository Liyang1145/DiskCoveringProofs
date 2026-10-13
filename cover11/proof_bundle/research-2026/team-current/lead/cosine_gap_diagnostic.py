"""Compare missing stresses versus cosine relaxation at three unresolved adversaries.
Numeric decision only: max3 new stress proposals, no large tree extension.
"""
from cosine_envelope_lp_diagnostic import solve,pairs
from certify_energy_cell import schur
from simplex_tree_pilot import *
import sys,math
import numpy as np
sys.path.insert(0,str(P.parent/'r20-alternative'))
from fixed_oracle_v2 import propose_from_widths

def main():
 tree=json.loads((P/'cosine_tree_pilot.json').read_text());fields=json.loads((P/'energy_library.json').read_text())['fields'];ns=[n for n in tree['nodes'] if n['status']=='split' and 'numeric_lower' in n];ns.sort(key=lambda n:n['numeric_lower']);sample=[ns[0],ns[len(ns)//2],ns[-1]];rows=[]
 for n in sample:
  v=[[F(x) for x in r] for r in n['vertices']];res=solve(v,fields);lam=res['lambda_numeric'];y=np.array([[float(x) for x in r] for r in v]).T@lam;th=np.array([float(lo(x)) for x in angles([F(float(t)) for t in y])]);g=np.array([1-math.cos(th[i]-th[j]) for i,j in pairs]);oldenergy=max(sum(2*float(F(w))*g[k] for k,(i,j,w) in enumerate(f['weights'])) for f in fields)
  sol=propose_from_widths([float(lo(L))-float(lo(D))*t for t in y]);ff=schur([[F(float(x)) for x in q] for q in sol['p_51']],'cosine_gap'+str(n['id']));ff['weights']=[(i,j,str(w)) for i,j,w in ff['weights']];new=solve(v,fields+[ff]);row={'node':n['id'],'old_relaxation':res['radius_lower_numeric'],'old_energy_at_adversary':math.sqrt(oldenergy),'point_oracle_numeric':sol['r'],'point_solver_success':sol['success'],'after_new_stress_relaxation':new['radius_lower_numeric'],'new_field':ff,'y_numeric':y.tolist()};rows.append(row);print({k:t for k,t in row.items() if k not in ['new_field','y_numeric']},flush=True)
 (P/'cosine_gap_diagnostic.json').write_text(json.dumps({'scope':'numeric diagnostic except exact stored Schur; no cell certificate','rows':rows},indent=2))
if __name__=='__main__':main()
