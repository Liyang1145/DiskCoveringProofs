"""Independent q10 clipping replay on immutable snapshot; partial coverage != global exclusion."""
from q11_split_inductive_audit import rowbasis,inv,sign,subtract,ZERO,Q,P,json
from q11_chord_flow_fraction_replay import replay
import hashlib,time

def value(n,v):return tuple(sum(n[j]*v[j][h]for j in range(10))for h in range(3))
def vs(p):return {tuple(tuple(map(Q,t))for t in v)for v in p['vertex_set']}
def audit():
 start=time.time();src=P/'q10-polytope-partition-879.json';raw=src.read_bytes();snapshot=P/'q10-polytope-partition-879-audit-snapshot.json';snapshot.write_bytes(raw);a=json.loads(raw);nodes=a['nodes'];pending=set(a['pending']);faces=json.loads((P/'k10-catalogue-corrected.json').read_text())['10/4'][879]['faces'];root=nodes[0]['polytope'];eq=([Q(1)]*10,(Q(10),Q(0),Q(-1)));expectedroot={tuple(eq[1]if j==i else ZERO for j in range(10))for i in range(10)};assert vs(root)==expectedroot;assert len(root['inequalities'])==10
 for j,(n,r,_)in enumerate(root['inequalities']):assert list(map(Q,n))==[Q(i==j)for i in range(10)]and tuple(map(Q,r))==ZERO
 assert tuple(map(Q,root['equality'][0]))==tuple(eq[0])and tuple(map(Q,root['equality'][1]))==eq[1]
 todo=[(0,expectedroot,root['inequalities'])];seen=set();leaves=[];openrows=[]
 while todo:
  j,VV,csraw=todo.pop();assert j not in seen;seen.add(j);node=nodes[j];assert node['id']==j
  if j in pending:
   assert 'status'not in node;openrows.append({'node':j,'vertices':len(VV)});continue
  poly=node['polytope'];assert vs(poly)==VV and poly['inequalities']==csraw and poly['equality']==root['equality'];assert node['flow_proposal']['faces']==faces and node['flow_proposal']['index']==879
  if node['status']!='split':
   assert node['status']=='leaf_bound_coverage_pending';c=node['certificate'];assert c['index']==879 and c['family']=='10/4'and c['flow']['faces']==faces;assert {tuple(tuple(map(Q,t))for t in v)for v in c['polytope']['vertices']}==VV;rr=replay(c);assert rr['excluded'];leaves.append({'node':j,'lower_exact':rr['lower_radius_exact']});continue
  VV=sorted(VV);cs=[(list(map(Q,n)),tuple(map(Q,r)),lab)for n,r,lab in csraw];rep=node['split_report'];normal=list(map(Q,rep['normal']));rhs=tuple(map(Q,rep['rhs']));active=[]
  for v in VV:
   assert value(eq[0],v)==eq[1];slacks=[subtract(value(n,v),r)for n,r,lab in cs];assert all(sign(s)>=0 for s in slacks);active.append({k for k,s in enumerate(slacks)if s==ZERO});assert len(rowbasis([eq[0]]+[cs[k][0]for k in active[-1]]))==10
  sides=[sign(subtract(value(normal,v),rhs))for v in VV];cross=set();cache={}
  for u in range(len(VV)):
   for v in range(u):
    if sides[u]*sides[v]!=-1:continue
    common=tuple(sorted(active[u]&active[v]))
    if len(common)<8:continue
    if common not in cache:
     rows=[eq[0]]+[cs[k][0]for k in common];cache[common]=(rows,rowbasis(rows))
    rows,br=cache[common]
    if len(br)!=9:continue
    rr=[eq[1]]+[cs[k][1]for k in common];MI=inv([rows[k]for k in br]+[normal]);assert MI is not None;bb=[rr[k]for k in br]+[rhs];w=tuple(tuple(sum(MI[i][k]*bb[k][h]for k in range(10))for h in range(3))for i in range(10));assert value(normal,w)==rhs and all(sign(subtract(value(n,w),r))>=0 for n,r,lab in cs);cross.add(w)
  for child,s in zip(node['children'],[1,-1]):
   expected={v for v,t in zip(VV,sides)if s*t>=0}|cross
   if child not in pending:
    cc=nodes[child]['polytope']['inequalities'];assert cc[:-1]==csraw;nn,rr,lab=cc[-1];assert list(map(Q,nn))==[s*x for x in normal]and tuple(map(Q,rr))==tuple(s*x for x in rhs)
   else:cc=csraw+[[list(map(str,[s*x for x in normal])),list(map(str,[s*x for x in rhs])),'audit_pending_cut']]
   todo.append((child,expected,cc))
  print('Q10CLIP',j,len(VV),len(cross),flush=True)
 assert seen==set(range(len(nodes)));out={'status':'independently_replayed_partial_partition_not_global_exclusion','snapshot_sha256':hashlib.sha256(raw).hexdigest(),'nodes':len(nodes),'excluded_leaves':leaves,'open_cells':openrows,'seconds':time.time()-start};(P/'q10-partial-partition-audit.json').write_text(json.dumps(out,indent=2));print('PARTIALAUDIT',len(nodes),len(leaves),len(openrows),flush=True)
if __name__=='__main__':audit()
