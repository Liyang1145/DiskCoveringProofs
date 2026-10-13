"""Exact polynomial-identity audit of the 3m+1 construction; no global lower bound."""
from pathlib import Path
import hashlib
import json
import sympy as S

ROOT=Path(__file__).resolve().parent
if not __debug__:
    raise RuntimeError("Assertions must be enabled")
c,s=S.symbols("c s",real=True)
den=5+12*c+8*c*c
t=1/den
a2=2*(1+c)*t
q=(S.Rational(3,2)+c,s*(1+2*c)/(2*(1+c)))
o=(0,0);i=(1,0);j=(c,s);h=(2,0);l=(1+c,s);hn=(2*c,2*s)
w0=(S.Rational(1,2),s/(2*(1+c)))
w1=(S.Rational(3,2),s/(2*(1+c)))
w2=(1+c-w0[0],s-w0[1])
w3=(c*w1[0]+s*w1[1],s*w1[0]-c*w1[1]) # reflection about bisector


def diff(p,q):
    return tuple(x-y for x,y in zip(p,q))


def dot(p,q):
    return sum(x*y for x,y in zip(p,q))


def reduce(poly):
    num,d=S.together(poly).as_numer_denom()
    rest=S.rem(S.Poly(num,s),S.Poly(s*s+c*c-1,s)).as_expr()
    return S.factor(rest/d)


def main():
    identities={"anchor_unit":a2*dot(q,q)-1,
                "anchor_high_distance":a2*dot(diff(q,h),diff(q,h))-t,
                "anchor_low_distance":a2*dot(diff(q,l),diff(q,l))-t}
    for k,(vertices,w) in enumerate((((o,i,j),w0),((i,h,l),w1),((i,l,j),w2),((j,l,hn),w3))):
        for z,p in enumerate(vertices):
            identities[f"face_{k}_distance_{z}"]=a2*dot(diff(w,p),diff(w,p))-t
    results={}
    for name,value in identities.items():
        r=reduce(value)
        assert r==0,(name,r)
        results[name]="0"
    x=S.symbols("x")
    minimal_c=8*c**3+4*c*c-4*c-1
    radius_cubic=29*x**3-55*x*x+19*x-1
    numerator=S.together(radius_cubic.subs(x,t)).as_numer_denom()[0]
    remainder=S.rem(S.Poly(numerator,c),S.Poly(minimal_c,c)).as_expr()
    assert remainder==0
    # Verify rather than treat a discovered decimal/minimal_polynomial as theorem.
    results["m7_radius_polynomial_divisibility"]="0"
    out={"verified":True,"field_relation":"c^2+s^2=1","parameter":"c=cos(2pi/m),s=sin(2pi/m),m>=6",
         "radius_squared":"1/(5+12c+8c^2)","inner_radius_squared":"2(1+c)/(5+12c+8c^2)",
         "identities":results,"m7_cosine_polynomial":str(minimal_c),
         "m7_radius_squared_polynomial":str(radius_cubic),"global_optimality_proved":False,
         "scope":"exact local geometric identities of a constructed family, not arbitrary-cover optimality",
         "source_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    target=ROOT/"evidence/symbolic-family-identities.json"
    assert not target.exists()
    target.write_text(json.dumps(out,indent=2),encoding="utf8")
    print("3m+1 constructed family: 15 geometric identities and cubic divisibility PASS",flush=True)


if __name__=="__main__":
    main()
