"""2D constrained TC Hessian on the exact C891 root; interval graph basis, no SVD certification."""
from pathlib import Path
import json,sys
from fractions import Fraction
from mpmath import mp,iv
P=Path(__file__).parent;sys.path.insert(0,str(P));import repair_tc_krawczyk as K
mp.dps=65;iv.dps=50
D=json.loads((P/'repaired_tc_krawczyk.json').read_text());C=D['certificate'];rad=float.fromhex(C['radius_hex']);U=[iv.mpf(float.fromhex(x))+iv.mpf([-rad,rad]) for x in C['center_hex']]
def ends(x):
 def rat(t):
  s,m,e,_=t;return (-1 if s else 1)*Fraction(m)*Fraction(2)**e
 return tuple(rat(t) for t in x._mpi_)
def positive(x):return ends(x)[0]>0
def record(x):
 return [str(q) for q in ends(x)]
def dec(x):return [float(q) for q in ends(x)]
f,J,hh=K.bundle(U[:7],True)
# Solve dependent coordinates a0..a3,R against free hub x-coordinates y0,y1.
dep=[0,1,2,3,6];free=[4,5]
A=[[J[i][k] for k in dep]+[-J[i][k] for k in free] for i in range(5)]
pivots=[]
for k in range(5):
 # fixed permutation chosen from interval-certified nonzero entries, not assumed rank
 options=[i for i in range(k,5) if ends(A[i][k])[0]>0 or ends(A[i][k])[1]<0]
 assert options
 pick=max(options,key=lambda i:min(abs(float(q)) for q in ends(A[i][k])))
 A[k],A[pick]=A[pick],A[k];p=A[k][k];pivots.append(record(p))
 for j in range(k+1,7):A[k][j]=A[k][j]/p
 A[k][k]=iv.mpf(1)
 for i in range(5):
  if i==k:continue
  v=A[i][k]
  for j in range(k+1,7):A[i][j]=A[i][j]-v*A[k][j]
  A[i][k]=iv.mpf(0)
Z=[[iv.mpf(0) for _ in range(2)] for _ in range(7)]
for i,k in enumerate(dep):Z[k]=A[i][5:]
for i,k in enumerate(free):Z[k][i]=iv.mpf(1)
H=[[-sum(U[7+k]*hh[k][i][j] for k in range(5)) for j in range(7)] for i in range(7)]
G=[[sum(Z[i][a]*H[i][j]*Z[j][b] for i in range(7) for j in range(7)) for b in range(2)] for a in range(2)]
det=G[0][0]*G[1][1]-G[0][1]*G[1][0]
assert positive(G[0][0]) and positive(det)
# Conservative rational lower bound on the smaller eigenvalue of symmetric G:
# lambda_min >= det/trace, since lambda_max<=trace when SPD.
tr=G[0][0]+G[1][1];lower=ends(det)[0]/ends(tr)[1]
assert lower>Fraction(1,4)
out={'scope':'C891 root TC boundary-saturated symmetric equality tangent only; NOT full local/global optimality','dependent':dep,'free':free,'pivots_exact':pivots,'basis_exact':[[record(x) for x in row] for row in Z],'gram_exact':[[record(x) for x in row] for row in G],'gram_display':[[dec(x) for x in row] for row in G],'det_exact':record(det),'det_display':dec(det),'lambda_min_lower_exact':str(lower),'lambda_min_lower_display':float(lower),'pass':True}
(P/'tc_symmetric_hessian.json').write_text(json.dumps(out,indent=2));print('Gram',out['gram_display'],'det',out['det_display'],'lambda_min>',float(lower))
