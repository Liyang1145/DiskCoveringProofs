from anchor_robust_flow_probe import *
from anchor_simplex_subdivision_probe import solve_node
src=json.loads((P/'anchor-robust-subdivision-warm-848.json').read_text());node=src['nodes'][255];local,_,_=solve_node(848,node['flow_proposal']['faces'],np.array(node['V']));local.update(index=848,family='10/4');out=[]
for mode in ['taylor','concave']:
 r=solve(local,10,mode,np.array(node['V']));r['mode']=mode;out.append(r)
(P/'q10-hard-flow-compare.json').write_text(json.dumps({'runs':out},indent=2))
