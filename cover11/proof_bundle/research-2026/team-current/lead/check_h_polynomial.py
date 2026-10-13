from pathlib import Path
import sympy as S,json
H,c1,c2,y1,y2,la,a1,a2,b1,b2,g1,g2=S.symbols('H c1 c2 y1 y2 la a1 a2 b1 b2 g1 g2')
x1=H-c1;x2=H-c2;q1=x1*x1+y1*y1;q2=x2*x2+y2*y2
p=(la+2*b1*x1+2*b2*x2)*q1*q2-a1*y1*q2-a2*y2*q1;u=g1*x1*q2;v=g2*x2*q1
# Avoidhugeexpand inallcoefficients; degreeviaunivariatepolynomial.
g=(p*p+u*u*q1-v*v*q2)**2-4*p*p*u*u*q1
r1,r2=S.symbols('r1 r2');F=p+u*r1+v*r2
# modulo definingr1²=q1,r2²=q2 andF=0 resultantidentity byremainder
# derive G vanishesatp=-u*r1-v*r2, thenreduce radicalquadratics.
P,U,V,Q1,Q2=S.symbols('P U V Q1 Q2');GG=(P*P+U*U*Q1-V*V*Q2)**2-4*P*P*U*U*Q1
rem=S.rem(S.rem(S.expand(GG.subs(P,-U*r1-V*r2)),r1*r1-Q1,r1),r2*r2-Q2,r2);assert S.expand(rem)==0
assert S.Poly(p,H).degree()==5
out={'radicaleliminationidentity':True,'degree_bound':20,'p_degree':5,'scope':'necessaryfixedparameterstationarypolynomial,notrootsorcontinuummax'};path=Path(__file__).parent/'h_polynomial_control.json';path.write_text(json.dumps(out,indent=2));print(out)
