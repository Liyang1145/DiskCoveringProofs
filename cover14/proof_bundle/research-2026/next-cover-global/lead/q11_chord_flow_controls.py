"""Onechord/twochord/no-chord3controls ofexactnewangularpolytope forrobustflowdesign."""
from anchor_robust_flow_probe import solve,P,json,np,math
from q11_chord_polytope import chord_middles,enumerate_vertices,iv,Q,S,L
rows=json.loads((P/'anchor-simplex-q11-catalogue-probe.json').read_text())['runs'];chosen=[]
for k in [2,1,0]:
 subset=[r for r in rows if len(chord_middles(r['faces']))==k]
 if subset:chosen.append(max(subset,key=lambda r:r['concave_vertex_lower_proposal']))
out=[]
for row in chosen:
 mid=chord_middles(row['faces']);poly=enumerate_vertices(mid);VV=np.array([[float(iv(tuple(map(Q,v))).lo/S)for v in V]for V in poly['vertices']]);ll=float(L.lo/S);TT=np.arange(11)*ll-np.c_[np.zeros(len(VV)),np.cumsum(VV[:,:-1],axis=1)];r=solve(row,11,'concave',angle_vertices=TT);r['polytope']=poly;out.append(r);(P/'q11-chord-flow-controls.json').write_text(json.dumps({'status':'numeric_reduced_polytope_flows','runs':out},indent=2));print('MID',mid,'vertices',len(VV),flush=True)
