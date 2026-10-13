"""Bounded controls: is persistent76 weakness due to forced anchorwise concavity? No tree mutation."""
from q11_polytope_partition_probe import *
if __name__=='__main__':
 a=json.loads((P/'q11-polytope-partition-76.json').read_text());nodes=[n for n in a['nodes']if n.get('status')=='split'];out=[]
 for n in [nodes[0]]+nodes[-3:]:
  row=n['flow_proposal'];poly=n['polytope'];VV=np.array([[float(iv(tuple(map(Q,t))).lo/S)for t in V]for V in poly['vertex_set']]);TT=np.arange(11)*float(L.lo/S)-np.c_[np.zeros(len(VV)),np.cumsum(VV[:,:-1],axis=1)];r=solve(row,11,'taylor',angle_vertices=TT);c=bound(r,{'vertices':poly['vertex_set']});rr=replay(c);out.append({'node':n['id'],'old_value':row['robust_value'],'taylor_value':r['robust_value'],'certificate':c,'replay':rr});print('CURVATURECONTROL',n['id'],row['robust_value'],r['robust_value'],c['lower_radius_display'],rr['excluded'],flush=True)
 (P/'q11-76-curvature-control.json').write_text(json.dumps({'status':'local_leaf_controls_not_treecoverage','runs':out},indent=2))
