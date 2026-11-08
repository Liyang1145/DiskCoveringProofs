"""Exact triangular-complex disk coverage certificate; pure rational arithmetic."""
import json
from fractions import Fraction as F
from collections import Counter,defaultdict
from pathlib import Path
if not __debug__:raise RuntimeError('Assertions required')
here=Path(__file__).resolve().parent; d=json.loads((here/'rational_geometry.json').read_text(encoding='utf8')); C=[tuple(map(F,p)) for p in d['centers']]; Q=[tuple(map(F,p)) for p in d['boundary_anchors']]; R=F(d['radius']); faces=d['faces']
assert len(C)==26 and len(Q)==16 and len(faces)==34 and R==F(234700091,10**9)
def sub(a,b):return a[0]-b[0],a[1]-b[1]
def dot(a,b):return a[0]*b[0]+a[1]*b[1]
def cross(a,b):return a[0]*b[1]-a[1]*b[0]
def dist2(a,b):return dot(sub(a,b),sub(a,b))
def circum(a,b,c):
 u=sub(b,a);v=sub(c,a);D=2*cross(u,v);assert D
 h=dot(b,b)-dot(a,a);k=dot(c,c)-dot(a,a)
 return ((h*v[1]-k*u[1])/D,(u[0]*k-v[0]*h)/D)
assert all(dot(c,c)<1 for c in C)
for i,q in enumerate(Q):
 assert dot(q,q)==1
 assert dist2(q,C[i])<=R*R and dist2(q,C[(i+1)%16])<=R*R
 nxt=Q[(i+1)%16]; assert cross(q,nxt)>0 and dot(q,nxt)>0
 prior=Q[(i-1)%16]; assert cross(prior,C[i])>0 and cross(C[i],q)>0
# The quadrant/half-plane pattern and strictly positive consecutive cross
# prove the 16 boundary anchors wind once counterclockwise.
assert [((q[0]>0)-(q[0]<0),(q[1]>0)-(q[1]<0)) for q in Q]==[(1,-1)]+[(1,1)]*4+[(-1,1)]*4+[(-1,-1)]*4+[(1,-1)]*3
witnesses=[]
for face in faces:
 assert len(face)==3 and len(set(face))==3 and all(0<=i<26 for i in face)
 p=circum(*(C[i] for i in face)); assert dot(p,p)<=1 and all(dist2(p,C[i])<=R*R for i in face)
 assert all((dist2(p,c)==dist2(p,C[face[0]]) if k in face else dist2(p,c)>dist2(p,C[face[0]])) for k,c in enumerate(C))
 witnesses.append(p)
assert len({tuple(sorted(face)) for face in faces})==34
points=Q+C
tri=[]
for i in range(16): tri.extend([((i-1)%16,i,16+i),(i,16+i,16+(i+1)%16)])
tri.extend(tuple(16+i for i in face) for face in faces)
# Orient the ABSTRACT triangles consistently. Geometric folding is allowed:
# degree of the map equals the boundary winding and proves coverage.
incidence=defaultdict(list)
for n,(a,b,c) in enumerate(tri):
 assert cross(sub(points[b],points[a]),sub(points[c],points[a])) != 0
 for x,y in ((a,b),(b,c),(c,a)):
  incidence[tuple(sorted((x,y)))].append((n,1 if x<y else -1))
orient={0:1}; todo=[0]
while todo:
 n=todo.pop(); a,b,c=tri[n]
 for x,y in ((a,b),(b,c),(c,a)):
  group=incidence[tuple(sorted((x,y)))]
  assert len(group) in (1,2)
  if len(group)==2:
   (i,di),(j,dj)=group
   other=j if i==n else i
   wanted=-orient[n]*di*dj
   if other in orient: assert orient[other]==wanted
   else:orient[other]=wanted;todo.append(other)
assert len(orient)==len(tri)
edges=Counter(); directions=Counter(); links=defaultdict(list)
for n,(a,b,c) in enumerate(tri):
 if orient[n]<0:b,c=c,b
 for x,y,z in ((a,b,c),(b,c,a),(c,a,b)):
  edges[tuple(sorted((x,y)))]+=1;directions[x,y]+=1;links[x].append((y,z))
assert len(tri)==66 and len(points)==42 and len(edges)==107 and 42-107+66==1
boundary={tuple(sorted((i,(i+1)%16))) for i in range(16)}
adj=defaultdict(set)
for (a,b),n in edges.items():
 assert n==(1 if (a,b) in boundary else 2)
 if (a,b) not in boundary:assert directions[a,b]==directions[b,a]==1
 adj[a].add(b);adj[b].add(a)
for i in range(16):assert directions[i,(i+1)%16]==1 and directions[(i+1)%16,i]==0
visited={0};todo=[0]
while todo:
 for x in adj[todo.pop()]:
  if x not in visited:visited.add(x);todo.append(x)
assert visited==set(range(42))
for i in range(42):
 e=links[i]; A=defaultdict(set)
 for a,b in e:A[a].add(b);A[b].add(a)
 visited={next(iter(A))};todo=list(visited)
 while todo:
  for x in A[todo.pop()]:
   if x not in visited:visited.add(x);todo.append(x)
 assert visited==set(A)
 if i<16:
  assert sorted(x for x in A if len(A[x])==1)==sorted(((i-1)%16,(i+1)%16))
  assert all(len(v) in (1,2) for v in A.values())
 else:assert all(len(v)==2 for v in A.values())
# Exact slack separation, not a claim of 134 contacts.
small=[]
for f,p in zip(faces,witnesses):
 if dist2(p,C[f[0]]) < F(232,1000)**2:small.append(f)
assert small==[[2,3,19],[5,6,21],[10,11,23],[13,14,25]]
assert all(dist2(p,C[face[0]]) > (R-F(1,10**6))**2 for face,p in zip(faces,witnesses) if face not in small)
assert all(dist2(Q[i],C[j]) > (R-F(1,10**6))**2 for i in range(16) for j in (i,(i+1)%16))
print('PASS: 26 disks of radius 234700091/10^9 cover unit disk')
print('42 vertices, 107 edges, 66 oriented triangles; 34 interior witnesses, 16 rational boundary anchors')
print('Four interior witnesses are strictly nearer than 0.232; 134 incidences are not 134 tight contacts')




