"""Independent Fraction enclosure of innernorm tangent constants.
Round interval endpoints outward before asin powers to keep exact integer sizes bounded.
"""
from area_safe_fraction_replay import F,pi,L,U,sqrtv,add,neg,mul,div,point,trig,P
import math,json
S=10**45
def roundiv(v):return(F((v[0].numerator*S)//v[0].denominator,S),F(-((-v[1].numerator*S)//v[1].denominator),S))
def sqrtiv(v):
 lo=math.isqrt((v[0].numerator*S*S)//v[0].denominator);hi=math.isqrt((v[1].numerator*S*S)//v[1].denominator)+1;return F(lo,S),F(hi,S)
def asin1(x,N=200):
 a=sum((F(math.comb(2*n,n),4**n*(2*n+1))*x**(2*n+1)for n in range(N)),F(0));return(a,a+x**(2*N+1)/(1-x*x))
def asiniv(v):
 v=roundiv(v);return roundiv((asin1(v[0])[0],asin1(v[1])[1]))
x=F('.458');sn,cs=map(roundiv,trig(x));z=mul(sqrtv,cs);av=add(add(point(x),neg(mul(point(F(1,2)),pi))),add(asiniv(z),mul(point(F(1,2)),L)))
ap=add(point(F(1)),neg(div(mul(sqrtv,sn),sqrtiv(add(point(F(1)),neg(mul(z,z)))))));ab=add(av,neg(mul(point(x),ap)))
x2=F('1.77');sn,cs=map(roundiv,trig(x2/2));z=mul(point(U),sn);bv=mul(point(F(2)),asiniv(z));bp=div(mul(point(U),cs),sqrtiv(add(point(F(1)),neg(mul(z,z)))));bb=add(bv,neg(mul(point(x2),bp)))
A=F('.135');k=F('.218');checks={'a_intercept':add(point(A),neg(ab)),'a_slope':add(point(k),neg(ap)),'b_intercept':add(point(A),neg(bb)),'b_slope':add(point(k),neg(bp)),'a_tangent_at_pi':add(add(ab,mul(pi,ap)),neg(L))}
assert all(v[0]>0 for v in checks.values())
if __name__=='__main__':
 (P/'innernorm-fraction-constants.json').write_text(json.dumps({'status':'exact_fraction_constants','A':str(A),'k':str(k),'margins':{key:list(map(str,roundiv(v)))for key,v in checks.items()}},indent=2));print({key:float(v[0])for key,v in checks.items()})
