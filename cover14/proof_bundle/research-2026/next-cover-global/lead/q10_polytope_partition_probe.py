"""Bounded q10 halfspace partitions compared with simplex longestedge split. No acceptedglobalconclusion."""
import sys,time
from q11_polytope_partition_probe import Polytope,default_decider,tri,midrange_split,solve,solve_case,P,json,np,Q,S,L,iv,bound,replay

def root():
 vv=[]
 for j in range(10):
  V=[tri()for _ in range(10)];V[j]=tri(10,0,-1);vv.append(tuple(V))
 return Polytope(10,vv,[([int(i==j)for i in range(10)],tri(),f'zero{j}')for j in range(10)],([1]*10,tri(10,0,-1)),default_decider(),'q10-879')
def angles(poly):
 VV=np.array([[float(iv(v).lo/S)for v in V]for V in poly.vertices]);return np.arange(10)*float(L.lo/S)-np.c_[np.zeros(len(VV)),np.cumsum(VV[:,:-1],axis=1)]
if __name__=='__main__':
 idx=879;row=next(r for r in json.loads((P/'anchor-simplex-q10-catalogue-probe.json').read_text())['runs']if r['index']==idx);polys=[root()];nodes=[{'id':0}];pending=[0];start=time.time()
 saved=P/'q10-polytope-partition-879.json'
 if saved.exists():
  prev=json.loads(saved.read_text());nodes=prev['nodes'];pending=prev['pending'];polys=[None]*len(nodes)
  for n in nodes:
   if 'polytope'in n:
    p=n['polytope'];polys[n['id']]=Polytope(10,[tuple(tuple(map(Q,t))for t in v)for v in p['vertex_set']],[(list(map(Q,nn)),tuple(map(Q,rr)),lab)for nn,rr,lab in p['inequalities']],(list(map(Q,p['equality'][0])),tuple(map(Q,p['equality'][1]))),default_decider(),row['case'])
  for n in nodes:
   if n.get('status')=='split'and any(polys[j]is None for j in n['children']):
    rep=n['split_report'];ge,le,_=polys[n['id']].split(list(map(Q,rep['normal'])),tuple(map(Q,rep['rhs'])),rep['label'])
    for j,p in zip(n['children'],[ge,le]):
     if polys[j]is None:polys[j]=p
 for step in range(63):
  if not pending:break
  k=pending.pop();poly=polys[k];TT=angles(poly);A=np.c_[np.cos(TT.mean(axis=0)),np.sin(TT.mean(axis=0))];nf=len(row['faces']);D=np.array(row['incidence_matrix']);rhs=np.vstack([np.zeros((3*nf,2)),np.repeat(A,2,axis=0)]);X=np.linalg.lstsq(D,rhs,rcond=None)[0];r=solve_case(row['case'],X[:14],A,row['faces'],row['owners'],X[14:]);r.update(index=idx,family='10/4');r=solve(r,10,'concave',angle_vertices=TT);n=nodes[k];n.update(polytope=poly.to_dict(),flow_proposal=r);c=bound(r,{'vertices':poly.to_dict()['vertex_set']})
  if c['status']!='excluded_pending_fraction_replay':
   from q10_smooth_flow_control import smooth
   sm=smooth(r,TT);cc=bound(sm,{'vertices':poly.to_dict()['vertex_set']})
   n['smooth_attempt']={'value':sm['smooth_value'],'success':sm['smooth_success'],'lower_radius_display':cc['lower_radius_display']}
   if cc['lower_radius_display']>c['lower_radius_display']:r=sm;c=cc;n['flow_proposal']=r
  if c['status']=='excluded_pending_fraction_replay':
   rr=replay(c);assert rr['excluded'];n.update(status='leaf_bound_coverage_pending',certificate=c,replay=rr)
  else:
   j=int(np.argmax(np.ptp(TT,axis=0)));normal=[int(i<j)for i in range(10)];ge,le,rep,rhs=midrange_split(poly,normal,f'node{k}_angle{j}');children=[]
   for p in [ge,le]:children.append(len(nodes));nodes.append({'id':len(nodes)});polys.append(p)
   n.update(status='split',split_report=rep,children=children);pending.extend(children)
  print('Q10POLY',k,'vertices',len(poly.vertices),'lb',c['lower_radius_display'],'pending',len(pending),flush=True);(P/'q10-polytope-partition-879.json').write_text(json.dumps({'status':'bounded_control_coverage_pending','nodes':nodes,'pending':pending,'seconds':time.time()-start},indent=2))
