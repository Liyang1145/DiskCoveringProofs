"""Global lower bound and exclusion of the ten-boundary-disk branch."""

from fractions import Fraction as F
from intervals import Interval as I

ZERO = I(0)
ONE = I(1)


def arctan_small(n):
    # Alternating series at x = 1/n. 36 terms give a lower bound.
    terms = [F((-1)**k, (2*k + 1) * n**(2*k + 1)) for k in range(37)]
    lo = sum(terms[:36])
    return I(lo, lo + terms[36])


PI = 16 * arctan_small(5) - 4 * arctan_small(239)

SERIES_TERMS = 12
coefficients = [F(1)]
for k in range(SERIES_TERMS - 1):
    coefficients.append(coefficients[-1] * F((2*k + 1)**2, 2*(k + 1)*(2*k + 3)))
COEFFICIENTS = tuple(map(I, coefficients))


def asin_at_most_one_over_sqrt2(x):
    # On 0 <= x <= 1/sqrt(2), the omitted tail is at most
    # 2*x*(x**2)**N since all coefficients are at most 1.
    x2 = x.square()
    value = ZERO
    for coeff in reversed(COEFFICIENTS):
        value = coeff + x2 * value
    main = x * value
    x8 = x2.square().square()
    tail = 2 * x * x8.square() * x8
    return I.raw(main.lo, main.hi + tail.hi)


def arc(cosine):
    # Cosines > 1 correspond to an empty arc. All arguments in this
    # certificate arise from circles with positive cosine half-angles.
    co = cosine.clamp(ZERO, ONE)
    si = ((1 - co) * (1 + co)).sqrt()
    angle = 2 * asin_at_most_one_over_sqrt2(((1 - co) / 2).sqrt())
    return angle, si, co


def on_unit(r, rho):
    return arc(1 - (r.square() - (1 - rho).square()) / (2 * rho))


def subdivide(initial, proved, scales):
    """Prove a predicate by a closed-box partition, or fail with an assertion."""
    stack = [initial]
    terminal = 0
    while stack:
        box = stack.pop()
        if proved(*box):
            terminal += 1
            continue
        axis = max(range(len(box)), key=lambda k: (box[k].hi - box[k].lo) * scales[k])
        assert box[axis].hi - box[axis].lo > (I.SCALE >> 28), box
        for half in box[axis].split():
            stack.append(box[:axis] + (half,) + box[axis + 1:])
    return terminal


def verify_ten():
    r = I("0.38")

    def ruled_out(p, rho, u):
        # u = cos(theta); v = cos(phi) for the directions from 0 and p.
        p2 = p.square()
        A, B = -I(".4") * p, -I(".14") * p
        K, C, D = I(".262") + I(".4") * p + 6 * p2, -3 * p - 6 * p2, 14 * p2
        al, sa, ca = on_unit(r, rho)
        dist = ((rho - p).square() + 2 * rho * p * (1 - u)).sqrt()
        be, sb, cb = arc(dist / (2 * r))
        v = ((rho * u - p) / dist).clamp(-ONE, ONE)
        value = (al + A * sa * u + B * sa * ca * (2 * u.square() - 1)
                 + K * (be - PI / 10)
                 + C * sb * v + D * sb * cb * (2 * v.square() - 1)
                 - PI / 10)
        return value.hi < 0

    # Endpoints suffice for the lower bound on the quadratic density.
    for p in (I(0), I(".14")):
        assert (I(".262") + I(".4") * p - 8 * p.square()
                - (3 + 6 * p).square() / 112).lo > 0
    count = subdivide((I(0, ".14"), I(".62", 1), I(-1, 1)), ruled_out, (4, 8, 1))
    print(f"Ten-boundary branch excluded at 19/50 ({count} verified boxes).")


def verify_small_separation():
    r, s = I(".38"), I(".448")

    def coefficients(p):
        p2 = p.square()
        A = -I(".75")*p+3*p2
        B = (8*p2).clamp(ZERO,I(".078"))
        K = I(".233")+I(".38")*p+I("1.95")*p2+I("2.1")*(p-I(".195")).nonnegative()
        C, D = -I("1.18")*p-I("7.6")*p2, I("7.9")*p2-I(".5")*p
        return A,B,K,C,D

    def positive(p, u):
        A,B,K,C,D = coefficients(p)
        return (1+A*u+B*(2*u.square()-1)).lo > 0 and (K+C*u+D*(2*u.square()-1)).lo > 0

    def below(p, rho, u):
        A,B,K,C,D = coefficients(p)
        al,sa,ca = on_unit(r,rho)
        q0,q1 = (I.raw(t,t) for t in (rho.lo,rho.hi))
        u0,u1 = (I.raw(t,t) for t in (u.lo,u.hi))
        d2lo = (p-q0*u1).square()+q0.square()*(1-u1.square())
        d2hi = (p-q1*u0).square()+q1.square()*(1-u0.square())
        d = I.raw(d2lo.lo,d2hi.hi).sqrt()
        d0,d1 = (I.raw(t,t) for t in (d.lo,d.hi))
        delta = s.square()-r.square()
        beta0 = (d0+delta/d0)/(2*s)
        beta1 = (d1+delta/d1)/(2*s)
        be,sb,cb = arc(I.raw(beta0.lo,beta1.hi))
        t = p/rho
        t0,t1 = (I.raw(w,w) for w in (t.lo,t.hi))
        v0 = (u0-t1)/((u0-t1).square()+1-u0.square()).sqrt()
        v1 = (u1-t0)/((u1-t0).square()+1-u1.square()).sqrt()
        v = I.raw(v0.lo,v1.hi).clamp(-ONE,ONE)
        value = (al+A*sa*u+B*sa*ca*(2*u.square()-1)
                 + K*(be-PI/9)+C*sb*v+D*sb*cb*(2*v.square()-1)-PI/9)
        return value.hi < 0

    n = subdivide((I(0,".208"),I(-1,1)),positive,(8,1))
    print(f"Small-separation weights positive ({n} verified boxes).")
    count = subdivide((I(0,".208"),I(".62",1),I(-1,1)),below,(5,9,1))
    print(f"Interior half-separation at most 0.068 excluded ({count} verified boxes).")


def verify_structure_constants():
    r = I(".38")
    alpha = arc((1 - r.square()).sqrt())[0]
    gamma = arc((1 - (2 * r).square()).sqrt())[0]
    h = 1 - r
    delta = arc((1 + h.square() - (3 * r).square()) / (2 * h))[0]
    for expression in (16 * alpha, 2 * gamma + 10 * alpha,
                       4 * gamma + 6 * alpha, 2 * delta + 8 * alpha):
        assert (expression - 2 * PI).hi < 0
    assert (alpha - I(".4")).hi < 0
    pmax, s = I(".14"), I(".48")
    assert (s.square() - (1 - 2*r)).hi < 0
    assert (pmax.square() + r.square() + pmax*r - s.square()).hi < 0
    max_k = I(".262") + I(".4") * pmax + 6 * pmax.square()
    assert (I(".4") * (1 + I(".54") * pmax)
            - PI / 5 + (PI / 3 - PI / 5) * max_k).hi < 0
    for cap, cosine in ((I(".187"), 1-2*r.square()),
                        (I(".282"), (1-r.square()).sqrt()*(1-4*r.square()))):
        assert cosine.lo > 0
        assert (1 + cap.square() + 2*cap*cosine - (3*r).square()).lo > 0
    assert (PI - I("3.1415926535")).lo > 0 and (I("3.1415926536") - PI).lo > 0
    assert (PI - I("3.141592653589793238")).lo > 0
    assert (I("3.141592653589793239") - PI).lo > 0
    print("Angular bounds for the outer diagonals verified.")


if __name__ == "__main__":
    verify_structure_constants()
    verify_ten()
    verify_small_separation()
