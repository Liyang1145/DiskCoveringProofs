"""C891 exact-root interval constants for finite adaptive-stress remainder lemma.
Imports bearing C912 kernel, then validates a larger ball. No neighborhood derivatives assumed.
"""
import interval_network_envelope as k
import numpy as np,json
iv=k.iv;mp=k.mp
I=lambda a,b=1:iv.mpf(a)/b
n=8;tau=I(1,10)
H=iv.matrix([[k.H[i,j] for j in range(n)] for i in range(n)]);G=k.G8
HH=H+2*tau*G*G.T
# Validate HH-muI positive definite by exact dyadic preconditioner and interval Gershgorin.
mu=I(1,500)
base=HH-mu*iv.eye(n);A=k.arr(base);Cn=np.linalg.inv(np.linalg.cholesky((A+A.T)/2)).T;C=iv.matrix(Cn.tolist());_,qC=k.solve(C,iv.eye(n));test=C.T*base*C
margin=min(k.lo(test[i,i]-sum(abs(test[i,j]) for j in range(n) if i!=j)) for i in range(n));assert margin>0
Q=tau*k.N*G.T
bdiag=max(k.hi(iv.sqrt(sum(Q[e,j]**2 for j in range(n)))/k.alpha[e]) for e in range(45))
# Anchor flux changes (not multiplied by2). Canonical radius units, no solver loads involved.
MM=iv.matrix(18,n);l0=iv.matrix(18,1);diag=[iv.mpf(0) for _ in range(9)]
for e,(v,w) in enumerate(k.edges):
 for node,sgn in [(v,1),(w,-1)]:
  if node>=9:continue
  dd=k.sub(k.X[v],k.X[w]);diag[node]+=k.alpha[e]
  for c in range(2):
   l0[2*node+c]+=sgn*k.alpha[e]*dd[c]
   for j in range(n):MM[2*node+c,j]+=sgn*Q[e,j]*dd[c]
mdiag=k.hi(iv.sqrt(sum(MM[i,j]**2 for i in range(18) for j in range(n))))
ddiag=max(k.hi(x) for x in diag)
arad=[sum(l0[2*i+c]*k.U[i][c] for c in range(2)) for i in range(9)]
assert min(k.lo(x) for x in arad)>0
# Select conservative rational ceilings independently verified by interval comparisons.
bQ=int(mp.ceil(bdiag));mQ=int(mp.ceil(mdiag*1000));dQ=int(mp.ceil(ddiag*1000))
assert max(iv.sqrt(sum(Q[e,j]**2 for j in range(n)))/k.alpha[e] for e in range(45))<=I(bQ)
assert iv.sqrt(sum(MM[i,j]**2 for i in range(18) for j in range(n)))<=I(mQ,1000)
assert max(diag)<=I(dQ,1000)
C3=I(dQ,1000)*(1+I(bQ))+I(mQ,1000)
# Choose dyadic denominator rational rho by conservative estimate, then exact interval recheck.
rho_den=10**6;rho_num=int(mp.floor(k.lo(mu/(4*C3))*rho_den))
assert rho_num>=1
rho=I(rho_num,rho_den)
assert I(bQ)*rho<1 and C3*rho<=mu/4
out={'status':'proved-interval constants, analytic lemma required','scope':'raw theta8-pinned Euclidean ball at exact C891 root; scalar carrying-energy lower bound to full51oracle; not global','constants':{'tau':'1/10','mu':'1/500','b':str(bQ),'m':str(mQ)+'/1000','d':str(dQ)+'/1000','rho':str(rho_num)+'/'+str(rho_den),'growth':'1/2000'},'diagnostics':{'b_upper':str(bdiag),'m_upper':str(mdiag),'d_upper':str(ddiag),'positive_hessian_margin':str(margin),'radial_min_lower':str(min(k.lo(x) for x in arad)),'remainder_coefficient_upper':str(k.hi(C3))},'premises':'C891,C909 exact root/equal carrying lengths/radial stationarity; interval kernel k for N,G,H; ADAPTIVE-STRESS-FINITE-REMAINDER.md'}
(k.P/'adaptive_stress_ball_certificate.json').write_text(json.dumps(out,indent=2));print(out,flush=True)
