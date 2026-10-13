"""Finite rational extraction + scalar route diagnostic. No lead module imports/writes."""
from pathlib import Path
from fractions import Fraction as F
import json, hashlib, math
HERE=Path(__file__).resolve().parent
LEAD=HERE.parents[1]/'lead'
files=['local-neighborhood-directional-4e5.json','local-neighborhood-directional-4e5-fraction-replay.json','dual-slack-localization-certificate.json','root-integer-certificate.json','root_integer_certificate.py','local_sosc_certificate.py','local_neighborhood_directional.py','fixed-anchor-flow-certificate.json']
x=json.loads((LEAD/files[0]).read_text()); W=[[F(v) for v in row] for row in x['W_exact']]
b=F(x['perron_bound']); n=len(W)
# Independently recompute the row majorant from the saved rational enclosure.
M=x['transformed_H_intervals']; v=list(map(F,x['perron_weights']))
E=[[max(abs(F(M[i][j][0])-int(i==j)),abs(F(M[i][j][1])-int(i==j))) for j in range(n)]for i in range(n)]
assert b==max(sum(E[i][j]*v[j] for j in range(n))/v[i] for i in range(n))<1
fro2=sum(w*w for row in W for w in row)
# Symmetric Gram absolute row bound gives a tighter certified ||W||_2^2 upper.
G=[[sum(W[k][i]*W[k][j] for k in range(n))for j in range(n)]for i in range(n)]
B=min(fro2,max(sum(abs(y)for y in row)for row in G))
h0=F(1,1000); mu=(1-b)/B; kappa=mu/(2*(1+27*h0))
# C1262: P>=mu/2 ||v||^2; P<=h+27h^2, 18 terms and K=3.
# Safe universal local rotation constants using source reference geometry: max|C*|<=1, s>=9/10.
K=F(29,9); eps=F(1,25000); tau=eps/K
# For repaired r <= U+e, e<=.001, squared excess <= .665 e.
U=F('0.33173203427623414'); root=json.loads((LEAD/files[3]).read_text()); rlo,rhi=map(F,root['box_dyadic'][2]); eta=U-rlo
assert 0<eta<F(1,10**15)
# Exact elementary cosine lower bound for delta<=1/1000.
repair_coefficient=1/(2*(1-F(1,1000)**2/8))
# Thus first exit D>=tau implies kappa*tau*D <= .665*(eta+a*delta^2).
coef=F(665,1000)/(kappa*tau)
# Read-only kernel import, with bytecode disabled by the documented -B command.
import sys
sys.dont_write_bytecode=True
sys.path.insert(0,str(LEAD))
from root_integer_certificate import I,S,calibrate
calibrate()
z,c,r=[I(int(F(lo)*S),int(F(hi)*S),True)for lo,hi in root['box_dyadic']]
s=(1-r*r).sqrt(); a=(s+z)/2; t=r+(r*r-z*z).sqrt()
bb=r+(r*r-(a-z)**2).sqrt(); dd=1-(r*r-c*c).sqrt()
assert s.lo>F(9,10)*S
for normsq in [a*a+bb*bb,c*c+dd*dd,s*s,z*z,t*t]:assert normsq.hi<S
v1=(1+a*a+bb*bb-r*r)/2; v2=(1+c*c+dd*dd-r*r)/2; det=a*dd-bb*c
px=(v1*dd-v2*bb)/det; py=(a*v2-c*v1)/det
A=[(s,r),(px,py),(I(0),I(1)),(-px,py),(-s,r),(-s,-r),(-px,-py),(I(0),I(-1)),(px,-py),(s,-r)]
for j in range(10):
 p,q=A[j],A[(j+1)%10]
 assert (p[0]*q[1]-p[1]*q[0]).lo>F(1,10)*S
 assert (p[0]*q[0]+p[1]*q[1]).lo>0
assert 2*rhi+F(1,10000)<F(665,1000)
assert F(665,1000)*(eta+repair_coefficient*F(1,1000)**2)<h0
rows=[]
for ds in ['0','0.000001','0.000003','0.00001','0.0001']:
 d=F(ds); bound=max(tau,coef*(eta+repair_coefficient*d*d))
 rows.append({'delta':ds,'conservative_D_upper_display':float(bound),'first_exit_rhs_over_tau':float(coef*(eta+repair_coefficient*d*d)/tau)})
# Anchor-only entry via the X+ opposite pair lens, then X+ gauge.
incidence=json.loads((LEAD/'fixed-anchor-flow-certificate.json').read_text())['runs'][0]
assert 9 in incidence['owners'][0] and 9 in incidence['owners'][9]
anchor_eps=F(2,10**6)
H=(U+anchor_eps)**2-rlo*rlo
sqrtH=I(H).sqrt(); sqrtHup=F(sqrtH.hi,S)
slo=F(s.lo,S)
xlo=slo-sqrtHup
alpha=(H/(2*rlo))/xlo
beta=anchor_eps+alpha
assert xlo>0 and beta<F(1,1000)
exit_rhs=F(665,1000)*(eta+repair_coefficient*beta*beta)
exit_lhs=kappa*eps*eps
assert exit_rhs<exit_lhs
final_site_squared=(U*U-rlo*rlo)/kappa
assert final_site_squared<F(1,10**7)**2
# Degenerate controls: radial repair vanishes at t=0,1 and delta=0;
# antipodal midpoint has zero norm and is deliberately outside delta<=.001.
assert 1-2*F(1,2)*(1-F(1,2))*(1-(-1))==0
slack=json.loads((LEAD/files[2]).read_text())
result={'scope':'rational consequences of SAVED C1262 Hessian enclosures; no independent AD/KKT; finite numeric display of derived constants, not global localization certificate',
'sources':{f:hashlib.sha256((LEAD/f).read_bytes()).hexdigest()for f in files},
'exact':{k:str(val)for k,val in dict(b=b,W_norm_squared_upper=B,mu=mu,h0=h0,kappa=kappa,K=K,tau=tau,U_minus_rstar_upper=eta,first_exit_coefficient=coef,repair_coefficient=repair_coefficient).items()},
'display':{k:float(val)for k,val in dict(W_norm_squared_upper=B,mu=mu,kappa=kappa,tau=tau,U_minus_rstar_upper=eta,first_exit_coefficient=coef,repair_coefficient=repair_coefficient).items()},
'finite_scalar_diagnostic':rows,
'anchor_only_2e6':{'status':'exact_rational_first_exit_inequality_passes_conditional_C1262_C1281','epsilon':str(anchor_eps),'gauge_angle_upper':str(alpha),'post_gauge_anchor_bound':str(beta),'exit_rhs':str(exit_rhs),'exit_lhs':str(exit_lhs),'display_ratio':float(exit_rhs/exit_lhs),'gauged_site_squared_upper':str(final_site_squared),'site_error_display':math.sqrt(float(final_site_squared))},
'old_dual_gauged_error_at_1e6':slack['gauged_error_display'],
'zero_eta_conservative_delta_for_localization_display':math.sqrt(float(kappa*tau*tau/(F(665,1000)*repair_coefficient)))}
(HERE/'diagnostic.json').write_text(json.dumps(result,indent=2))
print(json.dumps({'display':result['display'],'diagnostic':rows,'delta_threshold':result['zero_eta_conservative_delta_for_localization_display']},indent=2))
