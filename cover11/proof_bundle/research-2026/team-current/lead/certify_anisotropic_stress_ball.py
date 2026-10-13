"""Finite anisotropic remainder constants. No eigenvalue floating premise."""
import interval_network_envelope as k
import numpy as np,json
iv=k.iv;I=lambda a,b=1:iv.mpf(a)/b
n=8;t0=I(1,20);tau=I(1,10);mu=I(1,500)
H=iv.matrix([[k.H[i,j] for j in range(n)] for i in range(n)]);G=k.G8
base=H+2*t0*G*G.T-mu*iv.eye(n);A=k.arr(base);Cn=np.linalg.inv(np.linalg.cholesky((A+A.T)/2)).T;C=iv.matrix(Cn.tolist());_,qC=k.solve(C,iv.eye(n));test=C.T*base*C
assert min(k.lo(test[i,i]-sum(abs(test[i,j]) for j in range(n) if i!=j)) for i in range(n))>0
flux=iv.matrix(18,4);diag=[iv.mpf(0) for _ in range(9)]
for e,(v,w) in enumerate(k.edges):
 for node,sgn in [(v,1),(w,-1)]:
  if node>=9:continue
  diag[node]+=k.alpha[e];dd=k.sub(k.X[v],k.X[w])
  for c in range(2):
   for j in range(4):flux[2*node+c,j]+=sgn*k.N[e,j]*dd[c]
B=max(iv.sqrt(sum(k.N[e,j]**2 for j in range(4)))/k.alpha[e] for e in range(45))
Anorm=iv.sqrt(sum(flux[i,j]**2 for i in range(18) for j in range(4)))
Cross=iv.matrix(n,n)
for i in range(n):
 for j in range(n):Cross[i,j]=k.Lam[i,j]*(-k.U[i][1]*k.U[j][0]+k.U[i][0]*k.U[j][1])
cnorm=iv.sqrt(sum(Cross[i,j]**2 for i in range(n) for j in range(n)))
gnorm=iv.sqrt(sum(G[i,j]**2 for i in range(n) for j in range(4)))
def ceilr(x,den):return int(k.mp.ceil(k.hi(x)*den)),den
bq=ceilr(B,1);aq=ceilr(Anorm,1000);cq=ceilr(cnorm,10000);gq=ceilr(gnorm,1000);dq=ceilr(max(diag),1000)
BB,AA,CC,GG,dd=[I(a,b) for a,b in [bq,aq,cq,gq,dq]]
assert B<=BB and Anorm<=AA and cnorm<=CC and gnorm<=GG and max(diag)<=dd
# Check every component explicitly; do not rely on ordering overlapping intervals.
assert all(iv.sqrt(sum(k.N[e,j]**2 for j in range(4)))/k.alpha[e] <= BB for e in range(45))
assert all(v <= dd for v in diag)
quartic=dd/3+tau**2*(BB*dd+AA)**2/(4*(tau-t0))
# Determine a rational radius with positive growth then verify all inequalities.
rho_num=1
for num in range(1,1001):
 rho=I(num,100000)
 if not(tau*BB*GG*rho<1 and mu/2-CC*rho-quartic*rho**2>I(1,100000)):break
 rho_num=num
rho=I(rho_num,100000);growth=I(1,100000)
assert tau*BB*GG*rho<1 and mu/2-CC*rho-quartic*rho**2>growth
out={'scope':'local raw8 ball; analytic ANISOTROPIC-STRESS-REMAINDER lemma; not global','constants':{'tau':'1/10','tau0':'1/20','mu':'1/500','B':str(bq),'A':str(aq),'Ccross':str(cq),'G':str(gq),'d':str(dq),'rho':str(rho_num)+'/100000','growth':'1/100000'},'diagnostics':{'cross_upper':str(k.hi(cnorm)),'quartic_upper':str(k.hi(quartic)),'coefficient_lower':str(k.lo(mu/2-CC*rho-quartic*rho**2))}}
(k.P/'anisotropic_stress_ball_certificate.json').write_text(json.dumps(out,indent=2));print(out)
