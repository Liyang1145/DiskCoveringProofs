"""Exact interval obstruction to ANY fixed sharp nonnegative stress on literal graph.
D2 average -> symmetric central component; isolate normalized weights by6x6 rows;
fixed rational velocity certifies negative second variation. No float conclusion used.
"""
import json,numpy as np
from pathlib import Path
from fractions import Fraction
from root_integer_certificate import I,Q,S
P=Path(__file__).resolve().parent
cert=json.loads((P/'root-integer-certificate.json').read_text());X=[I(int(Q(a)*S),int(Q(b)*S),True)for a,b in cert['box_dyadic']]
z,c,r=X;s=(1-r*r).sqrt();a=(s+z)/2;t=r+(r*r-z*z).sqrt();b=r+(r*r-(a-z)**2).sqrt();d=1-(r*r-c*c).sqrt()
# Exact literal order, not root_cover_check order.
C=[(sx*a,sy*b)for sx in(-1,1)for sy in(-1,1)]+[(sx*c,sy*d)for sx in(-1,1)for sy in(-1,1)]+[(-s,I(0)),(s,I(0)),(z,I(0)),(-z,I(0)),(I(0),-t),(I(0),t)]
v1=(1+a*a+b*b-r*r)/2;v2=(1+c*c+d*d-r*r)/2;det=a*d-b*c
px=(v1*d-v2*b)/det;py=(a*v2-c*v1)/det
anc=[(s,r),(px,py),(I(0),I(1)),(-px,py),(-s,r),(-s,-r),(-px,-py),(I(0),I(-1)),(px,-py),(s,-r)]
# Strict inactive gaps; adjacent orientation positivity checked in root_cover_check.
for k in range(10):
 if k in(4,9):continue
 dot=sum(anc[k][j]*anc[(k+1)%10][j]for j in range(2))
 assert (dot-(1-2*r*r)).lo>0

def norm(p):return sum(x*x for x in p)
def sub(p,q):return [x-y for x,y in zip(p,q)]
def solve(M,v):
 A=[list(row)+[x]for row,x in zip(M,v)];n=len(v)
 for k in range(n):
  pivot=next(i for i in range(k,n)if A[i][k].lo*A[i][k].hi>0);A[k],A[pivot]=A[pivot],A[k]
  q=A[k][k];A[k]=[x/q for x in A[k]]
  for i in range(n):
   if i==k:continue
   q=A[i][k];A[i]=[x-q*y for x,y in zip(A[i],A[k])]
 return [row[-1]for row in A]
def mid(x):return (x.lo+x.hi)/(2*S)
g=json.loads((P/'stress-barycentric-result.json').read_text());sym=json.loads((P/'stress-symmetry-control.json').read_text())['symmetry_permutations_weights']
# Certify all14 tighttriangles acute, includingthe6whoseweightsvanish.
for face in g['faces']:
 ids=face['ids']
 for i in range(3):
  p=C[ids[i]];q=C[ids[(i+1)%3]];v=C[ids[(i+2)%3]]
  assert sum((q[j]-p[j])*(v[j]-p[j])for j in range(2)).lo>0
keep=[i for i in range(14)if i not in(1,4,7,10,12,13)]+[14+j for j,(k,i)in enumerate(( (k,i)for k,x in enumerate(g['anchors'])for i in x['owners']))if i not in(8,9)]
orbits=[];left=set(keep)
while left:
 orb={min(left)}
 while True:
  new=orb|{per[i]for i in orb for per in sym}
  if new==orb:break
  orb=new
 assert orb<=left;orbits.append(sorted(orb));left-=orb
assert len(orbits)==6
var={i:k for k,orb in enumerate(orbits)for i in orb}
# face variables are totalfaceweight; anchorvariables are edgeweight.
W={};B={};edges=[]
for f in keep:
 if f>=14:continue
 ids=g['faces'][f]['ids'];p,q,v=[C[i]for i in ids]
 w=solve([[2*(q[j]-p[j])for j in range(2)],[2*(v[j]-p[j])for j in range(2)]],[norm(q)-norm(p),norm(v)-norm(p)])
 beta=solve([[C[i][0]for i in ids],[C[i][1]for i in ids],[I(1)]*3],[*w,I(1)])
 assert all(bb.lo>0 for bb in beta);W[f]=w;B[f]=beta
 for i,bb in zip(ids,beta):edges.append((10+i,24+f,var[f],bb))
idx=14
for k,anchor in enumerate(g['anchors']):
 for i in anchor['owners']:
  if idx in keep:edges.append((k,10+i,var[idx],I(1)))
  idx+=1
pos={k:p for k,p in enumerate(anc)}|{10+k:p for k,p in enumerate(C)}|{24+k:p for k,p in W.items()}
rows=[]
for i in range(14):
 for axis in range(2):
  row=[I(0)for _ in range(6)]
  for u,v,j,bb in edges:
   if u==10+i:row[j]+=bb*(pos[u][axis]-pos[v][axis])
   elif v==10+i:row[j]+=bb*(pos[v][axis]-pos[u][axis])
  rows.append(row)
# Normalize firstface orbit=1. This excludes only zero central network, treated analytically.
rows.append([I(int(j==0))for j in range(6)])
# Numeric pivot proposal only; exactintervalelimination validates nonsingularity.
chosen=[28];mat=np.array([[mid(q)for q in row]for row in rows]);rank=1
for i in range(28):
 nr=np.linalg.matrix_rank(mat[chosen+[i]],tol=1e-10)
 if nr>rank:chosen.append(i);rank=nr
 if rank==6:break
assert rank==6
weights=solve([rows[i]for i in chosen],[I(int(i==28))for i in chosen]);assert all(w.lo>0 for w in weights)
# Need also prove face0 cannot vanish for nonzero symmetric central stress.
# Same invertible system with RHS0 forces allsixweights0, immediate.
used=sorted({x for u,v,j,bb in edges for x in(u,v)});free=[i for i in used if i>=10];boundary=[i for i in used if i<10]
L=np.zeros((len(used),len(used)));loc={x:i for i,x in enumerate(used)}
for u,v,j,bb in edges:
 w=mid(weights[j]*bb);ii,jj=loc[u],loc[v];L[ii,ii]+=w;L[jj,jj]+=w;L[ii,jj]-=w;L[jj,ii]-=w
ang=[Q(0),Q(-1,4),Q(-2,3),Q(-13,12),Q(-4,3),Q(-4,3),Q(-13,12),Q(-2,3),Q(-1,4),Q(0)]
vel={k:[-I(ang[k])*p[1],I(ang[k])*p[0]]for k,p in enumerate(anc)}
fi=[loc[i]for i in free];bi=[loc[i]for i in boundary]
raw=-np.linalg.solve(L[np.ix_(fi,fi)],L[np.ix_(fi,bi)]@np.array([[mid(q)for q in vel[i]]for i in boundary]))
# fixed rational velocity; NOT interval derivative of optimum needed.
for i,v in zip(free,raw):vel[i]=[I(Q(str(round(float(q),10))))for q in v]
curv=I(0)
for u,v,j,bb in edges:
 term=norm(sub(vel[u],vel[v]))
 if u<10:term-=I(ang[u]**2)*sum((pos[u][k]-pos[v][k])*pos[u][k]for k in range(2))
 if v<10:term-=I(ang[v]**2)*sum((pos[v][k]-pos[u][k])*pos[v][k]for k in range(2))
 curv+=2*weights[j]*bb*term
assert curv.hi<0
out={'status':'certified_negative_second_variation_symmetric_central_stress','scope':'selected literalgraph, fixed sharpnonnegative stress approach only; analytic D2averaging/zero-networkcases in STRESS-OBSTRUCTION.md required','orbits':orbits,'selected_equilibrium_rows':chosen,'normalized_weight_enclosures':[w.dec()for w in weights],'rational_anchor_angular_velocities':list(map(str,ang)),'free_velocity_dyadic':{str(i):[q.dec()for q in vel[i]]for i in free},'second_variation_exact_interval':curv.dec()}
(P/'stress-obstruction-certificate.json').write_text(json.dumps(out,indent=2));print('negative curvature certified',list(map(lambda q:float(Q(q)),curv.dec())),'orbits',orbits,'rows',chosen)
