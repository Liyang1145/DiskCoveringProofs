"""Independent complete activebasis reconstruction of splitpolytope children, no memberhelperimports."""
from q11_chord_polytope import Q,iv,nonneg,add,scale,combinations,P,json
import sys,hashlib,time

def inv(M):
 n=len(M);A=[[Q(x)for x in r]+[Q(i==j)for j in range(n)]for i,r in enumerate(M)]
 for j in range(n):
  p=next((i for i in range(j,n)if A[i][j]),None)
  if p is None:return None
  A[j],A[p]=A[p],A[j];s=A[j][j];A[j]=[x/s for x in A[j]]
  for i in range(n):
   if i!=j:
    s=A[i][j];A[i]=[x-s*y for x,y in zip(A[i],A[j])]
 return [r[n:]for r in A]
def enumerate_system(poly):
 cs=[(list(map(Q,n)),tuple(map(Q,r)),lab)for n,r,lab in poly['inequalities']];cuts=cs[22:];assert poly['equality']==[['1']*11,['11','0','-1']]
 for j in range(11):
  assert cs[2*j][:2]==([Q(i==j)for i in range(11)],(Q(0),)*3);assert cs[2*j+1][:2]==([-Q(i==j)for i in range(11)],(Q(-1),Q(0),Q(0)))
 vv=set();count=0
 # Since sumd=Delta<2L at mostonecoordinateequalsL. k active nonboxrows leave k+1 freevariables.
 for k in range(min(10,len(cuts))+1):
  for act in combinations(cuts,k):
   for free in combinations(range(11),k+1):
    M=[[Q(1)]*(k+1)]+[[n[j]for j in free]for n,r,lab in act];MI=inv(M)
    if MI is None:continue
    for full in [None]+[j for j in range(11)if j not in free]:
     count+=1;V=[(Q(0),)*3 for _ in range(11)]
     if full is not None:V[full]=(Q(1),Q(0),Q(0))
     rhs=[(Q(11-int(full is not None)),Q(0),Q(-1))]+[add(r,(-n[full],Q(0),Q(0)))if full is not None else r for n,r,lab in act]
     for j,row in zip(free,MI):V[j]=tuple(sum(a*b[h]for a,b in zip(row,rhs))for h in range(3))
     if any(not nonneg(v)or not nonneg(add((Q(1),Q(0),Q(0)),scale(v,-1)))for v in V):continue
     if any(not nonneg(tuple(sum(n[j]*V[j][h]for j in range(11))-r[h]for h in range(3)))for n,r,lab in cuts):continue
     vv.add(tuple(V))
 return vv,count
if __name__=='__main__':
 for idx in map(int,sys.argv[1:]or['510','75']):
  src=P/f'q11-polytope-partition-{idx}.json';a=json.loads(src.read_text());assert not a['pending'];records=[];start=time.time()
  for n in a['nodes']:
   vv,count=enumerate_system(n['polytope']);target={tuple(tuple(map(Q,t))for t in v)for v in n['polytope']['vertex_set']};assert vv==target;records.append({'node':n['id'],'vertices':len(vv),'bases':count,'exact_vertexsets_equal':True});print('AUDIT',idx,n['id'],len(vv),count,flush=True)
  (P/f'q11-split-basis-audit-{idx}.json').write_text(json.dumps({'status':'independent_complete_basis_vertexsets','source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'runs':records,'seconds':time.time()-start},indent=2))
