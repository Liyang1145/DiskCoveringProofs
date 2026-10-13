"""Bounded7node q11partitioncontrols; splitcoverage initially pendingseparateaudit."""
import sys,time,hashlib
from anchor_robust_flow_probe import solve,P,json,np
from fixed_anchor_convex_probe import solve_case
from q11_chord_polytope import chord_middles,enumerate_vertices,iv,Q,S,L
from q11_chord_flow_certificate import bound
from q11_chord_flow_fraction_replay import replay
sys.path.insert(0,str(P.parent/'members/dirichlet-cut-audit-cc2'))
from q11_polytope_split import Polytope,default_decider,tri,midrange_split

def root(row):
 poly=enumerate_vertices(chord_middles(row['faces']));ineq=[]
 for j in range(11):
  e=[0]*11;e[j]=1;ineq.append((e,tri(),f'zero{j}'));ineq.append(([-x for x in e],tri(-1),f'cap{j}'))
 for i in poly['middles_owner']:
  e=[int(j in {(i-2)%11,(i-1)%11,i})for j in range(11)];ineq.append((e,tri(3,-1),f'chord{i}'))
 return Polytope(11,[tuple(tuple(map(Q,v))for v in V)for V in poly['vertices']],ineq,([1]*11,tri(11,0,-1)),default_decider(),row['case'])
def floats(poly):
 VV=np.array([[float(iv(v).lo/S)for v in V]for V in poly.vertices]);return np.arange(11)*float(L.lo/S)-np.c_[np.zeros(len(VV)),np.cumsum(VV[:,:-1],axis=1)]
def local(row,TT):
 A=np.c_[np.cos(TT.mean(axis=0)),np.sin(TT.mean(axis=0))];nf=len(row['faces']);D=np.array(row['incidence_matrix']);rhs=np.vstack([np.zeros((3*nf,2)),np.repeat(A,2,axis=0)]);X=np.linalg.lstsq(D,rhs,rcond=None)[0];r=solve_case(row['case'],X[:14],A,row['faces'],row['owners'],X[14:]);r.update(index=row['index'],family='11/3');return r
if __name__=='__main__':
 for idx in map(int,sys.argv[1:]or['510','75']):
  start=time.time();row=next(r for r in json.loads((P/'anchor-simplex-q11-catalogue-probe.json').read_text())['runs']if r['index']==idx);polys=[root(row)];nodes=[{'id':0}];pending=[0];processed=0
  saved=P/f'q11-polytope-partition-{idx}.json'
  if saved.exists():
   prev=json.loads(saved.read_text());nodes=prev['nodes'];pending=prev['pending'];processed=prev['processed'];polys=[None]*len(nodes)
   for n in nodes:
    if 'polytope'in n:
     p=n['polytope'];polys[n['id']]=Polytope(11,[tuple(tuple(map(Q,t))for t in v)for v in p['vertex_set']],[(list(map(Q,nn)),tuple(map(Q,rr)),lab)for nn,rr,lab in p['inequalities']],(list(map(Q,p['equality'][0])),tuple(map(Q,p['equality'][1]))),default_decider(),row['case'])
   for n in nodes:
    if n.get('status')=='split'and any(polys[j]is None for j in n['children']):
     rep=n['split_report'];ge,le,_=polys[n['id']].split(list(map(Q,rep['normal'])),tuple(map(Q,rep['rhs'])),rep['label'])
     for j,p in zip(n['children'],[ge,le]):
      if polys[j]is None:polys[j]=p
  stop=processed+31
  while pending and processed<stop:
   k=pending.pop();poly=polys[k];TT=floats(poly);r=solve(local(row,TT),11,'concave',angle_vertices=TT);node=nodes[k];node.update(polytope=poly.to_dict(),flow_proposal=r);processed+=1;domain={'status':'splitpolytope_vertexcoverage_pending','vertices':poly.to_dict()['vertex_set']};c=bound(r,domain)
   if c['status']=='excluded_pending_fraction_replay':
    rr=replay(c);assert rr['excluded'];node.update(status='leaf_bound_certified_coverage_pending',certificate=c,replay=rr)
   else:
    j=int(np.argmax(np.ptp(TT,axis=0)));normal=[int(i<j)for i in range(11)];ge,le,rep,rhs=midrange_split(poly,normal,f'node{k}_angle{j}');assert ge is not None and ge.vertices and le.vertices;children=[]
    for p in [ge,le]:children.append(len(nodes));nodes.append({'id':len(nodes)});polys.append(p)
    node.update(status='split',split_report=rep,children=children);pending.extend(children)
   (P/f'q11-polytope-partition-{idx}.json').write_text(json.dumps({'status':'bounded_partition_probe_coverage_audit_pending','index':idx,'nodes':nodes,'pending':pending,'processed':processed,'seconds':time.time()-start},indent=2));print('NODE',idx,k,'vertices',len(poly.vertices),'status',node['status'],'bound',c['lower_radius_display'],flush=True)
  print('DONE',idx,processed,'pending',len(pending),'seconds',time.time()-start,flush=True)
