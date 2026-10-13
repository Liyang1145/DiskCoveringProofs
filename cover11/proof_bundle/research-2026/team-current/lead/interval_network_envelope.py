"""Exact-root interval network interface. All conclusions explicitly in output.
No residual interval containing zero is used to infer a rank upper bound/identity.
"""
from pathlib import Path
import json
import numpy as np
from scipy.linalg import qr
from mpmath import mp,iv
mp.dps=70;iv.dps=50
P=Path(__file__).resolve().parent
cert=json.loads((P/'repaired_tc_krawczyk.json').read_text())['certificate']
rad=float.fromhex(cert['radius_hex'])
u=[iv.mpf(float.fromhex(x))+iv.mpf([-rad,rad]) for x in cert['center_hex']];z=u[:7];R=z[6]
a=[z[0],z[1],z[2],z[3],iv.pi-2*sum(z[:4]),z[3],z[2],z[1],z[0]]
th=[iv.mpf(0) for _ in range(9)]
for k in range(5,9):th[k]=th[k-1]+a[k-1]+a[k]
for k in range(3,-1,-1):th[k]=th[k+1]-a[k]-a[k+1]
rho=[iv.cos(x)-iv.sqrt(R*R-iv.sin(x)**2) for x in a]
C=[(rho[k]*iv.cos(th[k]),rho[k]*iv.sin(th[k])) for k in range(9)]+[(z[4],iv.mpf(0)),(z[5],iv.mpf(0))]
U=[(iv.cos(th[k]+a[k]),iv.sin(th[k]+a[k])) for k in range(9)]
F=[[2,9,10],[6,9,10]]+[[k,(k+1)%9,9 if 2<=k<=5 else 10] for k in [1,2,3,4,5,6,8]]
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def sub(a,b):return tuple(x-y for x,y in zip(a,b))
def cc(f):
 a,b,c=[C[k] for k in f];v=sub(b,a);w=sub(c,a);d=(dot(b,b)-dot(a,a))/2;e=(dot(c,c)-dot(a,a))/2;det=v[0]*w[1]-v[1]*w[0]
 return ((d*w[1]-e*v[1])/det,(v[0]*e-w[0]*d)/det)
Z=[cc(f) for f in F];X=U+C+Z
edges=[]
for k in range(9):edges.extend([(9+k,k),(9+(k+1)%9,k)])
for j,f in enumerate(F):edges.extend((9+s,20+j) for s in f)
def zeros(n,m):return iv.matrix(n,m)
def lo(x):return mp.mpf(x.a)
def hi(x):return mp.mpf(x.b)
def mid(x):return (lo(x)+hi(x))/2
def mag(x):return max(abs(lo(x)),abs(hi(x)))
def arr(A):return np.array([[float(mid(A[i,j])) for j in range(A.cols)] for i in range(A.rows)])
def norminf(A):return max(hi(sum(abs(A[i,j]) for j in range(A.cols))) for i in range(A.rows))
def solve(M,b):
 # Validated real inverse and solution by Banach perturbation: C=exact dyadic inverse of midpoint (merely preconditioner).
 Cn=np.linalg.inv(arr(M));Ci=iv.matrix(Cn.tolist());E=iv.eye(M.rows)-Ci*M;q=hi(iv.mpf(norminf(E))+iv.mpf('1e-40'))
 assert q<mp.mpf('.01'),q
 y=iv.matrix((Cn@arr(b)).tolist());v=Ci*(b-M*y);eps=hi(iv.mpf(norminf(v))/(1-iv.mpf(q)))
 # Initial rigorous uniform enclosure; componentwise fixed-point refinement preserves enclosure.
 corr=iv.matrix([[iv.mpf([-eps,eps]) for j in range(b.cols)] for i in range(b.rows)])
 for _ in range(12):corr=v+E*corr
 return y+corr,q
B=zeros(41,45);T=zeros(9,45)
for j,(v,w) in enumerate(edges):
 d=sub(X[v],X[w])
 for node,sgn in [(v,1),(w,-1)]:
  if node>=9:
   for k in range(2):B[2*(node-9)+k,j]+=sgn*d[k]
  else:T[node,j]+=2*sgn*dot(d,(-U[node][1],U[node][0]))
 B[40,j]=1
# Four independent angular rows select unique radial stress. Existence of all-row solution is analytic C909.
_,_,piv=qr(np.vstack((arr(B),arr(T))).T,pivoting=True)
# Force all B rows, then select tangent rows by greedy rank of midpoint (selection only).
rows=list(range(41));M0=arr(B)
for k in range(9):
 trial=np.vstack((M0,arr(T)[k]))
 if np.linalg.matrix_rank(trial,tol=1e-8)>len(rows):rows.append(41+k);M0=trial
 if len(rows)==45:break
assert len(rows)==45
All=iv.matrix([[B[i,j] if i<41 else T[i-41,j] for j in range(45)] for i in range(50)])
M=iv.matrix([[All[i,j] for j in range(45)] for i in rows]);b=zeros(45,1);b[40,0]=1
alpha,q=solve(M,b)
assert min(lo(alpha[j]) for j in range(45))>mp.mpf('.0029')
print('radial stress enclosed; alpha min',mp.nstr(min(lo(alpha[j]) for j in range(45)),12),'contraction',mp.nstr(q,5),flush=True)
# Exact normalized stress affine tangent basis from invertible 41-column subsystem of B.
_,_,cols=qr(arr(B),pivoting=True);dep=list(map(int,cols[:41]));free=list(map(int,cols[41:]))
BD=iv.matrix([[B[i,j] for j in dep] for i in range(41)]);BF=iv.matrix([[-B[i,j] for j in free] for i in range(41)])
ND,qB=solve(BD,BF);N=zeros(45,4)
for i,j in enumerate(dep):
 for k in range(4):N[j,k]=ND[i,k]
for k,j in enumerate(free):N[j,k]=1
G=T*N
# Exact ker(G.T) in fixed theta8 chart. Parametrize using4 free angular coordinates.
_,_,ac=qr(arr(G).T[:,:8],pivoting=True);adep=list(map(int,ac[:4]));afree=list(map(int,ac[4:]))
GD=iv.matrix([[G[j,i] for j in adep] for i in range(4)]);GF=iv.matrix([[-G[j,i] for j in afree] for i in range(4)])
KD,qG=solve(GD,GF);K=zeros(9,4)
for i,j in enumerate(adep):
 for k in range(4):K[j,k]=KD[i,k]
for k,j in enumerate(afree):K[j,k]=1
# Schur energy uses all20 carrying free nodes, no isolated slack auxiliary.
L=zeros(29,29)
for j,(v,w) in enumerate(edges):
 al=alpha[j];L[v,v]+=al;L[w,w]+=al;L[v,w]-=al;L[w,v]-=al
Lff=iv.matrix([[L[i,j] for j in range(9,29)] for i in range(9,29)])
Lfa=iv.matrix([[L[i,j] for j in range(9)] for i in range(9,29)])
Y,qL=solve(Lff,Lfa);Lam=iv.matrix([[L[i,j] for j in range(9)] for i in range(9)])-Lfa.T*Y
H=zeros(9,9)
for i in range(9):
 for j in range(9):
  if i!=j:H[i,j]=2*Lam[i,j]*dot(U[i],U[j])
for i in range(9):H[i,i]=-sum(H[i,j] for j in range(9) if i!=j)
HK=K.T*H*K
# Congruence with numerical inverse Cholesky only as an exact dyadic preconditioner, then interval Gershgorin.
Hkm=arr(HK);Qn=np.linalg.inv(np.linalg.cholesky((Hkm+Hkm.T)/2)).T;Q=iv.matrix(Qn.tolist());test=Q.T*HK*Q
lower=min(lo(test[i,i]-sum(abs(test[i,j]) for j in range(4) if i!=j)) for i in range(4))
assert lower>mp.mpf('.95'),lower
# Q nonsingularity needs proof too, not merely numerical cholesky.
_,qQ=solve(Q,iv.eye(4))
# Conservative rational explicit local patch constants.
G8=iv.matrix([[G[i,j] for j in range(4)] for i in range(8)])
GramInv,qGram=solve(G8.T*G8,iv.eye(4))
sigma=lo(1/iv.sqrt(iv.mpf(norminf(GramInv))))
nmax=max(mag(N[i,j]) for i in range(45) for j in range(4))
eps=lo(iv.mpf('.001')/iv.mpf(nmax))
KQ=K*Q
mu=lo(iv.mpf('.95')/sum(KQ[i,j]**2 for i in range(9) for j in range(4)))
c1=lo(iv.mpf(eps)*iv.mpf(sigma)/2);Mbound=hi(2/iv.mpf(c1))
# Power-of-ten radius; certify the complete split-lemma inequality directly.
rho=mp.mpf('0.01')
while hi((2*iv.mpf(Mbound)+iv.mpf('.5'))*iv.mpf(rho)+(iv.mpf(mu)/2+1)*iv.mpf(Mbound)**2*iv.mpf(rho)**2)>mu/4:rho/=10
assert hi(iv.mpf(eps)*iv.mpf(nmax))<mp.mpf('.0029')
# Bearing assertions use exact rational interval constants, not the printed diagnostics above.
assert iv.mpf(sigma)>iv.mpf(1)/4
assert mu>mp.mpf(1)/600  # enormous separation from rounding; direct interval comparison below too
assert iv.mpf(mu)>iv.mpf(1)/600
assert iv.mpf(nmax)/1000<iv.mpf('.0029')
rhoQ=iv.mpf(1)/10**8;muQ=iv.mpf(1)/600;MQ=iv.mpf(16000)
assert (2*MQ+iv.mpf('.5'))*rhoQ+(muQ/2+1)*MQ**2*rhoQ**2<muQ/4
quant={'certified_rational_constants':{'eps':'1/1000','sigma':'1/4','mu':'1/600','c1':'1/8000','M':'16000','rho':'1/100000000','growth':'1/2400'},'sigma_lower':str(sigma),'eps':str(eps),'mu_lower':str(mu),'c1_lower':str(c1),'M_upper':str(Mbound),'rho_power10':str(rho),'qGram':str(qGram)}
out={'quantitative_local_patch':quant,'scope':'interval at exact C891 root; radial existence/balance identities from C909; selected-subsystem ranks proved by contraction. With NETWORK-ENVELOPE-QUANTITATIVE-LEMMA.md, fixed-theta8 chart radius1e-8 has V^2>=R*^2+||x||^2/2400. Local only; no globalP coverage.', 'alpha_min_lower_diagnostic':str(min(lo(alpha[j]) for j in range(45))),'alpha_min_gt_.0029':True,'force_balance_rank':40,'normalized_stress_dimension':4,'angular_gradient_rank':4,'critical_angle_dimension_mod_rotation':4,'preconditioned_HK_Gershgorin_gt_.95':True,'preconditioned_HK_lower_diagnostic':str(lower),'contractions_diagnostic':[str(v) for v in [q,qB,qG,qL]],'stress_free_columns':free,'angle_dependent_columns':adep,'angle_free_columns':afree,'faces':F,'edges':edges,'alpha_intervals_diagnostic':[[str(lo(alpha[j])),str(hi(alpha[j]))] for j in range(45)]}
(P/'interval_network_envelope.json').write_text(json.dumps(out,indent=2))
print({k:v for k,v in out.items() if k not in ['alpha_intervals_diagnostic','edges','faces']},flush=True)
