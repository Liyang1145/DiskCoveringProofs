"""Exact active-basis vertex enumeration for q11 chord-gapdomain; symbolic(L,B,2pi)."""
from area_safe_certificate import I,Q,S,PI,L,U,asin,P
from itertools import combinations,permutations
import numpy as np,json
B=2*asin(2*U);G=3*L-B;assert (2*PI-B-7*L).lo>0 and(G-(10*L-2*PI)).lo>0 and(L-G).lo>0

def iv(v):return v[0]*L+v[1]*B+v[2]*(2*PI)
def add(a,b):return tuple(x+y for x,y in zip(a,b))
def scale(a,s):return tuple(x*s for x in a)
def nonneg(v):
 if not any(v):return True
 z=iv(v)
 assert not z.lo<=0<=z.hi,('unresolvedsign',v,z.dec())
 return z.lo>0

def determinant(M):
 n=len(M)
 return sum((-1)**sum(p[i]>p[j]for i in range(n)for j in range(i+1,n))*__import__('math').prod(int(M[i][p[i]])for i in range(n))for p in permutations(range(n)))

def chord_middles(faces):
 edges={tuple(sorted(e))for f in faces for e in combinations(f,2)if max(e)<11};mid=[]
 for i in range(11):
  if tuple(sorted(((i-1)%11,(i+1)%11)))in edges:mid.append(i)
 return mid

def enumerate_vertices(middles):
 triples=[{(i-2)%11,(i-1)%11,i}for i in middles];verts=set();basiscount=0
 for k in range(len(triples)+1):
  for act in combinations(range(len(triples)),k):
   for free in combinations(range(11),k+1):
    M=np.array([[1]*(k+1)]+[[int(j in triples[c])for j in free]for c in act]);det=determinant(M)
    if not det:continue
    adj=np.rint(np.linalg.inv(M)*det).astype(int);assert np.array_equal(M@adj,det*np.eye(k+1,dtype=int));inv=[[Q(int(v),det)for v in rr]for rr in adj]
    bounded=[j for j in range(11)if j not in free]
    for full in [None]+bounded:
     basiscount+=1;V=[(Q(0),)*3 for j in range(11)]
     if full is not None:V[full]=(Q(1),Q(0),Q(0))
     rhs=[(Q(11-int(full is not None)),Q(0),Q(-1))]+[(Q(3-int(full in triples[c])),Q(-1),Q(0))for c in act]
     for j,rr in zip(free,inv):V[j]=tuple(sum(rr[a]*rhs[a][b]for a in range(k+1))for b in range(3))
     if any(not nonneg(v)or not nonneg(add((Q(1),Q(0),Q(0)),scale(v,-1)))for v in V):continue
     if any(not nonneg(add(tuple(sum(V[j][a]for j in tr)for a in range(3)),(Q(-3),Q(1),Q(0))))for tr in triples):continue
     verts.add(tuple(V))
 return {'middles_owner':middles,'triples_gap':[sorted(t)for t in triples],'vertex_count':len(verts),'basis_count':basiscount,'vertices':[[[str(x)for x in v]for v in V]for V in sorted(verts)]}
if __name__=='__main__':
 out=[enumerate_vertices(m)for m in [[],[1],[1,3]]];(P/'q11-chord-polytope-controls.json').write_text(json.dumps({'status':'symbolic_complete_activebasis_vertices','constants':{'L':L.dec(),'B':B.dec(),'margin_Bplus7L':(2*PI-B-7*L).dec()},'runs':out},indent=2));print([(x['middles_owner'],x['vertex_count'],x['basis_count'])for x in out])
