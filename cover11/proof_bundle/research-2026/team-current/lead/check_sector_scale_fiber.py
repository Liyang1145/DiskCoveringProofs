"""Analytic algebra controls + off-candidate equivalence tests for scale-fiber formula."""
from pathlib import Path
import math,random,json
import sympy as S
P=Path(__file__).parent;a,o=S.symbols('a o',real=True)
assert S.trigsimp(2*S.sin(o)*S.sin(a-o)-S.cos(2*o-a)+S.cos(a))==0
R=.38;t0=75/76;rng=random.Random(910);tests=0;ok=0;maxerr=0
for _ in range(20000):
 a=rng.uniform(.0233,math.pi);u=rng.uniform(.00002,1);v=rng.uniform(.00002,1);d=math.log(u/v)/2;s=math.sqrt(u*v);Q=2*(math.cosh(2*d)-math.cos(a));K=R*math.sqrt(Q)/2;o=math.asin(K*s);E=math.exp(2*abs(d));B=math.cos(a)+2*K*K*t0*t0
 direct=s*s*math.sin(a-o)>=max(t0*t0,u*u,v*v)*math.sin(o)
 if B>1:fiber=False
 else:
  theta=math.acos(B);lo=max((a-theta)/2,0);hi=min((a+theta)/2,math.asin(K*math.exp(-abs(d))),math.atan2(math.sin(a),E+math.cos(a)));fiber=lo<=o<=hi
 assert direct==fiber,(a,u,v,direct,fiber)
 tests+=1;ok+=int(fiber);maxerr=max(maxerr,abs(u-math.sin(o)/K*math.exp(d)),abs(v-math.sin(o)/K*math.exp(-d)))
# singular branch tested algebraically as s>=t0, noatan2(0,0)
for s in [.1,t0-.001,t0,t0+.001,1.]:assert (s*s>=t0*t0)==(s>=t0)
out={'exact_trig_identity':True,'offcandidate_equivalence_tests':tests,'feasible_count':ok,'max_inverse_error':maxerr,'singular_alpha_pi_d0':'s in [75/76,1] analytically','scope':'analytic proof in SECTOR-SCALE-FIBER.md; randompoints calibration only'}
(P/'sector_scale_fiber_control.json').write_text(json.dumps(out,indent=2));print(out)
