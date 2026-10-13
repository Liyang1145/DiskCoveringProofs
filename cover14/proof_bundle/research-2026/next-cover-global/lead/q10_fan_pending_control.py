"""Four pendingcell controls measure structuralcut leverage, without mutating acceptedtree."""
from q10_fan_domain import *
from q10_polytope_partition_probe import Polytope,default_decider,angles,solve,solve_case,np,bound,replay
if __name__=='__main__':
 a=json.loads((P/'q10-polytope-partition-879.json').read_text());nodes=a['nodes'];targets=set(a['pending'][:4]);out=[];row=next(r for r in json.loads((P/'anchor-simplex-q10-catalogue-probe.json').read_text())['runs']if r['index']==879)
 for n in nodes:
  if n.get('status')!='split'or not any(i in targets for i in n['children']):continue
  p=n['polytope'];poly=Polytope(10,[tuple(tuple(map(Q,t))for t in v)for v in p['vertex_set']],[(list(map(Q,nn)),tuple(map(Q,rr)),lab)for nn,rr,lab in p['inequalities']],(list(map(Q,p['equality'][0])),tuple(map(Q,p['equality'][1]))),default_decider(),'879');rep=n['split_report'];children=poly.split(list(map(Q,rep['normal'])),tuple(map(Q,rep['rhs'])),rep['label'])[:2]
  for j,cp in zip(n['children'],children):
   if j not in targets:continue
   original=len(cp.vertices);rhs=tuple(Q(5,24)*x for x in tri(10,0,-1))
   for ids in [[8,9,0,1],[3,4,5,6]]:cp,_,_=cp.split([int(i in ids)for i in range(10)],rhs,'fan'+str(ids[0]))
   if not cp.vertices:out.append({'node':j,'empty_after_cuts':True});continue
   TT=angles(cp);AA=np.c_[np.cos(TT.mean(axis=0)),np.sin(TT.mean(axis=0))];nf=len(row['faces']);D=np.array(row['incidence_matrix']);rhs=np.vstack([np.zeros((3*nf,2)),np.repeat(AA,2,axis=0)]);X=np.linalg.lstsq(D,rhs,rcond=None)[0];r=solve_case(row['case'],X[:14],AA,row['faces'],row['owners'],X[14:]);r.update(index=879,family='10/4');r=solve(r,10,'concave',angle_vertices=TT);c=bound(r,{'vertices':cp.to_dict()['vertex_set']});rr=replay(c);out.append({'node':j,'original_vertices':original,'polytope':cp.to_dict(),'certificate':c,'replay':rr});print('FANCELL',j,original,len(cp.vertices),c['lower_radius_display'],flush=True)
 (P/'q10-fan-pending-control.json').write_text(json.dumps({'status':'four_local_controls_coverage_pending','runs':out},indent=2))
