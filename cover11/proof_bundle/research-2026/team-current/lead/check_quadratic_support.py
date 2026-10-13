"""Independent Fraction control for interval Q=max Ay²+By on[0,1]."""
from fractions import Fraction as F
from pathlib import Path
import random,json
P=Path(__file__).parent
# Load only arithmetic kernel definitions, without graphs or global certificate loop.
s=(P/'certify_shared_moments_dense.py').read_text();part=s[s.index('def pos('):s.index('# interval polynomial/trigonometric')]
from mpmath import iv
iv.dps=25
import math
exec(part)
def exact(a,b):
 vals=[F(0),a+b]
 if a<0 and 0<b<-2*a:vals.append(-b*b/(4*a))
 return max(vals)
def ivrat(q):return iv.mpf(q.numerator)/q.denominator
rng=random.Random(719);n=0
for i in range(3000):
 a,b,c,d=[F(rng.randrange(-500,501),128) for _ in range(4)];a,c=sorted([a,c]);b,d=sorted([b,d]);got=quad(interval(ivrat(a).a,ivrat(c).b),interval(ivrat(b).a,ivrat(d).b))
 for A,B in [(a,b),(c,d),((a+c)/2,(b+d)/2)]:
  true=ivrat(exact(A,B));assert got.a<=true.b and true.a<=got.b,(A,B,got,true)
 n+=1
(P/'quadratic_support_control.json').write_text(json.dumps({'rational_boxes':n,'analytic_comparator':'Fraction endpoints plus valid stationary vertex','passed':True},indent=2));print(n,'quadratic coefficient boxes checked against independent Fraction support')
