"""Attack a weakq10/848 leaf: tenvertex primalcontrols, oneoutermin frombest; bounded."""
from anchor_simplex_subdivision_probe import solve_node,P,json,np
from anchor_outer_local_probe import run
src=json.loads((P/'anchor-robust-subdivision-warm-848.json').read_text());node=src['nodes'][255];faces=node['flow_proposal']['faces'];out=[]
for j,v in enumerate(node['V']):
 row,_,_=solve_node(848,faces,np.tile(v,(10,1)));row.update(index=848,family='10/4');out.append(row);print(j,row['radius'],flush=True)
(P/'q10-hard-vertex-attack.json').write_text(json.dumps({'status':'numeric_primal_vertex_controls','source_node':255,'runs':out},indent=2))
