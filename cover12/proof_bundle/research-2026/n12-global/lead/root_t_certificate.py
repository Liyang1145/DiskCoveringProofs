"""Exact rational-grid Krawczyk certification for F,G,H,T, independent of J root.
Contraction + self-map proves unique root in specified closed rational box.
"""
from stress_interval import I,F,verify
import sympy as S,json
from pathlib import Path
P=Path(__file__).resolve().parents[1]
a,t,r,w=S.symbols('a t r w');xs=(a,t,r,w)
b=(1+a+r)/2;ss=b*b+w*w/3;AA=3*b*b-w*w-2*b*w
polys=[a*a+a*r-a*t-2*r*t+t*t,(1+t*t-r*r)*(3*b*b+w*w)-t*(3*b*b-w*w+6*b*w),4*w*w-12*r*r+3*(1-a-r)**2,w*ss*ss*(2*a-t+r)*(1-t*t-r*r)+(ss-b)*(2*t-2*r-a)*t*t*AA]
polys=[S.Poly(S.expand(p),*xs).clear_denoms()[1].as_expr() for p in polys]
J=S.Matrix(polys).jacobian(xs)
def form(p):
 return [(F(int(c.p),int(c.q)),mon) for mon,c in S.Poly(p,*xs).terms()]
def ev(p,box):
 z=I(0)
 for c,mon in p:
  term=I(c)
  for x,n in zip(box,mon):term*=x**n
  z+=term
 return z
center=[F(round(F(v)*10**35),10**35) for v in json.loads((P/'evidence/d3-chart-calibration.json').read_text())['root']] # exact grid-aligned center, no silent box enlargement
rad=F(1,10**30);box=[I(v-rad,v+rad) for v in center];ci=list(map(I,center))
# Rational inverse computed at exact rational center, then rounded to35 decimals (arbitrary fixed preconditioner).
num=J.subs(dict(zip(xs,[S.Rational(v.numerator,v.denominator) for v in center]))).evalf(60).inv()
Y=[[F(str(num[i,j].evalf(36))) for j in range(4)] for i in range(4)]
f=[ev(form(p),ci) for p in polys];JI=[[ev(form(J[i,j]),box) for j in range(4)] for i in range(4)]
B=[[I(int(i==j))-sum((I(Y[i][k])*JI[k][j] for k in range(4)),I(0)) for j in range(4)] for i in range(4)]
q=max(sum(max(abs(v.lo),abs(v.hi)) for v in row) for row in B);assert q<1
K=[ci[i]-sum((I(Y[i][k])*f[k] for k in range(4)),I(0))+sum((B[i][j]*I(-rad,rad) for j in range(4)),I(0)) for i in range(4)]
assert all(x.lo<z.lo and z.hi<x.hi for x,z in zip(box,K))
# ||I-YJ||<1 implies YJ invertible hence Y invertible; roots of x-Yf=x are f=0.
out={'status':'certified','proposition':'unique root of F,G,H,T in input rational box by Banach contraction; exact root belongs to Krawczyk image','vars':['a','t','r','w'],'polynomials':[str(p) for p in polys],'box':[v.dump() for v in box],'image':[v.dump() for v in K],'preconditioner':[[str(v) for v in row] for row in Y],'contraction_norm_upper':str(q),'selfmap_margins':[str(min(z.lo-x.lo,x.hi-z.hi)) for x,z in zip(box,K)]}
(P/'evidence/root-t-certificate.json').write_text(json.dumps(out,indent=2))
aa,tt,rr,ww=box;bb=(1+aa+rr)/2
assert aa.lo>0 and tt.lo>0 and rr.lo>0 and ww.lo>0
assert (bb-ww).lo>0 # beta in(0,pi/6), hence alpha>0
assert rr.hi<F('0.361102963744508672616920293904')
assert rr.hi<F(1,2)
stress=verify([v.dump() for v in box]);(P/'evidence/root-t-stress-certificate.json').write_text(json.dumps(stress,indent=2))
print(json.dumps({'status':out['status'],'q_float_display':float(q),'strict_selfmap':True,'stress_status':stress['status']}))
