"""Exact algebra control and geometric calibration of isolated-switch coupling."""
from pathlib import Path
import sympy as S, random,math,json
P=Path(__file__).parent
rho,c,b=S.symbols('rho c b',real=True)
# c denotes cos(b); symmetric endpoints have norm² 1+rho²−2rho c.
assert S.expand((1-rho*c)**2+rho**2*(1-c*c)-(1+rho*rho-2*rho*c))==0
R=.38;tau=75/76;rng=random.Random(1101);n=0
for _ in range(10000):
 t=rng.uniform(.001,1);b=rng.uniform(0,math.pi/2);cc=math.cos(b);D=cc*cc-R*R*tau*tau
 direct=2*t*cc>=R*(t*t+max(t*t,tau*tau))
 if D<0:fiber=False
 else:
  root=math.sqrt(D);lo=R*tau*tau/(cc+root);hi=min(1,cc/R,(cc+root)/R);fiber=lo<=t<=hi
 assert direct==fiber
 if direct:
  r=max(.375,R*t);norm2=1+(R*t)**2-2*R*t*cc
  assert norm2<=1-r*r+1e-14
 n+=1
out={'exact_symmetric_norm_identity':True,'fiber_equivalence_controls':n,'scope':'analytic proof in INWARD-SWITCH-COUPLING.md; numeric controls not continuumproof'}
(P/'switch_coupling_control.json').write_text(json.dumps(out,indent=2));print(out)
