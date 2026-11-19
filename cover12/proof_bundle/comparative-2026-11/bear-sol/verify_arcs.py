"""Integer-only verification of weighted concentric-circle arc bounds."""

from bisect import bisect_left
from math import factorial

from verify_upper import I

STEP = 10**32  # angle step 0.0001 in the fixed-point scale

CERTIFICATES = (
    ("0.354", 9, [(394,251),(409,314),(427,249),(445,259),(465,225),
                 (485,194),(505,166),(525,136),(545,107),(565,68),(1000,8031)]),
    ("0.354", 10, [(320,446),(331,323),(341,310),(351,153),(363,261),
                  (374,473),(385,337),(409,96),(430,307),(457,265),(484,197),
                  (511,195),(538,87),(559,88),(1000,6462)]),
    ("0.361103", 11, [(302,161),(309,442),(322,465),(337,339),(352,125),
                     (369,180),(381,42),(394,567),(408,624),(420,618),(1000,6437)]),
)


def sincos(x):
    x2 = x*x
    a,b = x,I(1)
    s,c = a,b
    for k in range(1, 24):
        a = -a*x2/((2*k)*(2*k+1))
        b = -b*x2/((2*k-1)*(2*k))
        s = s+a
        c = c+b
    # Taylor through degrees 47 (sine) and 46 (cosine), with |x| <= 4.
    assert -4*I.scale <= x.a <= x.b <= 4*I.scale
    e = -(-(4**47*I.scale)//factorial(47))
    return s+I.make(-e,e), c+I.make(-e,e)


def trig_table():
    # The elementary bound 3 < pi < 4 and the signs isolate pi here.
    assert sincos(I("3.1415926"))[0].pos()
    assert (-sincos(I("3.1415927"))[0]).pos()
    sd,cd = sincos(I.make(STEP,STEP))
    s,c = I(0),I(1)
    out = []
    for _ in range(31416):  # 0 through 3.1415, radians
        out.append(-c.b)
        s,c = s*cd+c*sd,c*cd-s*sd
    assert all(y > x for x,y in zip(out,out[1:]))
    return out


def upper_angle(cosine_lower, table):
    if cosine_lower >= I.scale:
        return 0
    j = bisect_left(table,-cosine_lower)
    return j*STEP


def arc_on_bin(k, t, a, b, table):
    """Upper half-angle on d in [a,b]; k=t^2-r^2."""
    assert k.a == k.b and t.a == t.b and 0 <= a <= b
    if k.b < 0:
        if a == 0:
            return 31416*STEP
        v = I.make(a,a)
        w = (v+k/v)/(2*t)
    else:
        assert k.a > 0  # all radii tested are different from r
        if b == 0:
            return 0
        if b*b <= k.a*I.scale:
            v = I.make(b,b)
            w = (v+k/v)/(2*t)
        elif a*a >= k.a*I.scale:
            v = I.make(a,a)
            w = (v+k/v)/(2*t)
        else:
            w = k.sqrt()/t
    return upper_angle(w.a,table)


def max_weight(r, test, lo, hi, table):
    assert lo < hi and r.a == r.b
    data = [(t*t-r*r, t, w) for t,w in test]
    assert all(w >= 0 for _,_,w in data)
    step = I.scale//8000
    best = 0
    for a in range(lo,hi,step):
        b = min(a+step,hi)
        best = max(best, sum(w*arc_on_bin(k,t,a,b,table) for k,t,w in data))
    return best


def checks():
    table = trig_table()
    # At the larger radius the bound of eight arcs is still strictly below pi.
    r = I("0.361103")
    q = (1-r*r).sqrt()
    assert 8*upper_angle(q.a,table) < I("3.1415926").a
    for radius,m,certificate in CERTIFICATES:
        r = I(radius)
        cut = (1-r).a
        inner_hi = (3*r-1).a if m == 11 else cut
        test = [(I(t)/1000,w) for t,w in certificate]
        total = sum(w for t,w in test)
        bound = m*max_weight(r,test,cut,I.scale,table)
        bound += (12-m)*max_weight(r,test,0,inner_hi,table)
        margin = total*I("3.1415926").a-bound
        assert margin > 0
        print(f"PASS: r={radius}, m={m}, normalized angular margin > "
              f"{margin*10**6//(total*I.scale)}e-6 radians")
    print("PASS: R > 0.354; at r <= 0.361103 there cannot be 11 or 12 outer disks")
    r = I("0.361103")
    A = upper_angle((1-r*r).sqrt().a,table)
    d = I("0.70")
    low_alpha = arc_on_bin(1-r*r,I(1),(1-r).a,d.a,table)
    low = low_alpha+upper_angle((1-(r/(1-r))*(r/(1-r))).sqrt().a,table)
    high = A+upper_angle((1-(r/d)*(r/d)).sqrt().a,table)
    assert 12*A+2*max(low,high)<2*I("3.1415926").a
    print("PASS: angular bound excluding distant outer-disk intersections")
    return table


if __name__ == "__main__":
    checks()
