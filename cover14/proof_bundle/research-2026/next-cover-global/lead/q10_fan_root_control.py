"""Structuralcut exactvertexcalibration and one robustflow control, no global conclusion."""
from q10_fan_domain import *
from q10_polytope_partition_probe import angles,solve,solve_case,np,bound,replay
if __name__=='__main__':
 poly,reports=fan_root();A=[8,9,0,1];B=[3,4,5,6];C=[2,7];delta=tri(10,0,-1);scale=lambda f:tuple(f*x for x in delta);expected=set()
 for i in A:
  for j in B:
   for k in C:
    v=[tri()for _ in range(10)];v[i]=scale(Q(5,24));v[j]=scale(Q(5,24));v[k]=scale(Q(7,12));expected.add(tuple(v))
   for t in [Q(5,24),Q(19,24)]:
    v=[tri()for _ in range(10)];v[i]=scale(t);v[j]=scale(1-t);expected.add(tuple(v))
 assert set(poly.vertices)==expected and len(expected)==64
 row=next(r for r in json.loads((P/'anchor-simplex-q10-catalogue-probe.json').read_text())['runs']if r['index']==879);TT=angles(poly);AA=np.c_[np.cos(TT.mean(axis=0)),np.sin(TT.mean(axis=0))];nf=len(row['faces']);D=np.array(row['incidence_matrix']);rhs=np.vstack([np.zeros((3*nf,2)),np.repeat(AA,2,axis=0)]);X=np.linalg.lstsq(D,rhs,rcond=None)[0];r=solve_case(row['case'],X[:14],AA,row['faces'],row['owners'],X[14:]);r.update(index=879,family='10/4');r=solve(r,10,'concave',angle_vertices=TT);c=bound(r,{'vertices':poly.to_dict()['vertex_set']});rr=replay(c);out={'status':'independent_closedform_vertices_verified_leafbound_only','vertices':64,'proposal':r,'certificate':c,'replay':rr};(P/'q10-fan-root-control.json').write_text(json.dumps(out,indent=2));print('FANBOUND',c['lower_radius_display'])
