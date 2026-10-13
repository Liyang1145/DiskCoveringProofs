"""C1331/C1332 necessaryclosedmetricdomain, Q³ arithmetic. No sharpboundclaimed."""
from q10_fan_domain import fan_root,tri,Q,P,json
from q10_smooth_flow_control import smooth
from q10_polytope_partition_probe import angles,solve_case,np,bound,replay

def reduced_root():
 poly,reports=fan_root();rhs=tuple(-Q(1,2)*x for x in tri(10,0,-1))
 for ids in [[0,1,2],[2,3,4],[5,6,7],[7,8,9]]:
  poly,_,rep=poly.split([-int(i in ids)for i in range(10)],rhs,'C1332upper'+str(ids[0]));reports.append(rep)
 return poly,reports
if __name__=='__main__':
 poly,reports=reduced_root();out={'status':'C1331_C1332_necessarydomain_vertices_pendingindependentaudit','polytope':poly.to_dict(),'reports':reports};(P/'q10-reduced-metric-domain.json').write_text(json.dumps(out,indent=2));print('REDUCEDROOT',len(poly.vertices),flush=True)
 row=next(r for r in json.loads((P/'anchor-simplex-q10-catalogue-probe.json').read_text())['runs']if r['index']==879);TT=angles(poly);AA=np.c_[np.cos(TT.mean(axis=0)),np.sin(TT.mean(axis=0))];nf=len(row['faces']);D=np.array(row['incidence_matrix']);rhs=np.vstack([np.zeros((3*nf,2)),np.repeat(AA,2,axis=0)]);X=np.linalg.lstsq(D,rhs,rcond=None)[0];r=solve_case(row['case'],X[:14],AA,row['faces'],row['owners'],X[14:]);r.update(index=879,family='10/4');r=smooth(r,TT);c=bound(r,{'vertices':poly.to_dict()['vertex_set']});rr=replay(c);out.update(proposal=r,certificate=c,replay=rr);(P/'q10-reduced-metric-domain.json').write_text(json.dumps(out,indent=2));print('REDUCEDBOUND',c['lower_radius_display'],flush=True)
