"""Independent exact clipping replay: reconstruct every crossing edge by common-active rank.
No member imports. Calibrated against completeactivebasis on510/75 andhard311/434.
Rootcompletevertices from independentlyauditedchorddomain. Everychild recursivelyverified.
"""
from q11_chord_polytope import Q,P,json,iv,chord_middles,enumerate_vertices
from q11_split_basis_audit import inv
import sys,hashlib,time
ZERO=(Q(0),)*3
def verts(poly):return {tuple(tuple(map(Q,t))for t in v)for v in poly['vertex_set']}
def sign(t):
 if t==ZERO:return 0
 v=iv(t);assert not v.lo<=0<=v.hi
 return 1 if v.lo>0 else -1
def value(n,v):return tuple(sum(n[j]*v[j][h]for j in range(11))for h in range(3))
def subtract(a,b):return tuple(x-y for x,y in zip(a,b))
def rowbasis(rows):
 piv=[];basis=[]
 for k,rr in enumerate(rows):
  r=list(rr)
  for j,v in piv:
   if r[j]:s=r[j];r=[x-s*y for x,y in zip(r,v)]
  j=next((i for i,x in enumerate(r)if x),None)
  if j is not None:
   s=r[j];r=[x/s for x in r];piv.append((j,r));basis.append(k)
 return basis

def audit(idx):
 start=time.time();src=P/f'q11-polytope-partition-{idx}.json';a=json.loads(src.read_text());assert not a['pending'];nodes=a['nodes'];root=enumerate_vertices(chord_middles(nodes[0]['flow_proposal']['faces']));assert verts(nodes[0]['polytope'])=={tuple(tuple(map(Q,t))for t in v)for v in root['vertices']};todo=[0];seen=set();records=[]
 while todo:
  j=todo.pop();assert j not in seen;seen.add(j);node=nodes[j];poly=node['polytope'];VV=sorted(verts(poly))
  if node['status']!='split':records.append({'node':j,'vertices':len(VV),'exact_vertexsets_equal':True});continue
  cs=[(list(map(Q,n)),tuple(map(Q,r)),lab)for n,r,lab in poly['inequalities']];eq=([Q(1)]*11,(Q(11),Q(0),Q(-1)));rep=node['split_report'];normal=list(map(Q,rep['normal']));rhs=tuple(map(Q,rep['rhs']));active=[]
  for v in VV:
   assert value(eq[0],v)==eq[1];slacks=[subtract(value(n,v),r)for n,r,lab in cs];assert all(sign(s)>=0 for s in slacks);active.append({k for k,s in enumerate(slacks)if s==ZERO});assert len(rowbasis([eq[0]]+[cs[k][0]for k in active[-1]]))==11
  sides=[sign(subtract(value(normal,v),rhs))for v in VV];cross=set();cache={};edges=0
  for u in range(len(VV)):
   for v in range(u):
    if sides[u]*sides[v]!=-1:continue
    common=tuple(sorted(active[u]&active[v]))
    if len(common)<9:continue
    if common not in cache:
     rows=[eq[0]]+[cs[k][0]for k in common];br=rowbasis(rows);cache[common]=(rows,br)
    rows,br=cache[common]
    if len(br)!=10:continue
    edges+=1;rr=[eq[1]]+[cs[k][1]for k in common];M=[rows[k]for k in br]+[normal];MI=inv(M);assert MI is not None;bb=[rr[k]for k in br]+[rhs];w=tuple(tuple(sum(MI[i][k]*bb[k][h]for k in range(11))for h in range(3))for i in range(11));assert value(normal,w)==rhs;assert all(sign(subtract(value(n,w),r))>=0 for n,r,lab in cs);cross.add(w)
  for child,s in zip(node['children'],[1,-1]):
   cp=nodes[child]['polytope'];expected={v for v,t in zip(VV,sides)if s*t>=0}|cross;assert verts(cp)==expected,(idx,j,child,len(expected),len(verts(cp)));assert cp['inequalities'][:-1]==poly['inequalities'];nn,rr,lab=cp['inequalities'][-1];assert list(map(Q,nn))==[s*x for x in normal]and tuple(map(Q,rr))==tuple(s*x for x in rhs)
  todo.extend(node['children']);records.append({'node':j,'vertices':len(VV),'exact_vertexsets_equal':True,'crossing_edges':edges,'crossing_vertices':len(cross)});print('CLIP',idx,j,len(VV),edges,flush=True)
 assert seen==set(range(len(nodes)));out={'status':'independent_inductive_complete_clipping_vertexsets','source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'runs':records,'seconds':time.time()-start};(P/f'q11-split-inductive-audit-{idx}.json').write_text(json.dumps(out,indent=2));print('DONECLIP',idx,len(nodes),time.time()-start,flush=True)
if __name__=='__main__':
 for idx in map(int,sys.argv[1:]or['510','75']):audit(idx)
