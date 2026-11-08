"""Exact numerical premises of the Voronoi area lower bound.

The companion AREA-PROOF.md supplies the geometric reduction. This program
does not replace that reduction: it verifies every numerical premise with
standard-library rational arithmetic, including pi, trigonometry and roots.
"""
from fractions import Fraction as F
from math import isqrt
import json

if not __debug__:
    raise RuntimeError("Assertions must be enabled")


def atan_inverse(q, terms=36):
    partial = sum((F((-1)**j, (2*j+1)*q**(2*j+1))
                   for j in range(terms)), F(0))
    remainder = F(1, (2*terms+1)*q**(2*terms+1))
    return ((partial, partial+remainder) if terms % 2 == 0
            else (partial-remainder, partial))


a, b = atan_inverse(5), atan_inverse(239)
machin_lo, machin_hi = 16*a[0]-4*b[1], 16*a[1]-4*b[0]
PI_LO = F(314159265358979323846, 10**20)
PI_HI = PI_LO + F(1, 10**20)
assert PI_LO < machin_lo < machin_hi < PI_HI


def sin_bounds(x):
    # 0<=x<=1: alternating terms decrease strictly in absolute value.
    assert 0 <= x <= 1
    term = x
    partial = term
    for k in range(1, 12):
        term *= -x*x / ((2*k)*(2*k+1))
        partial += term
    return partial, partial + x**25/F(15511210043330985984000000)


def cos_bounds(x):
    assert 0 <= x <= 1
    term = F(1)
    partial = term
    for k in range(1, 12):
        term *= -x*x / ((2*k-1)*(2*k))
        partial += term
    return partial, partial + x**24/F(620448401733239439360000)


def root_bounds(x, scale=10**24):
    assert x >= 0
    k = isqrt(x.numerator*scale**2 // x.denominator)
    lo, hi = F(k, scale), F(k+1, scale)
    assert lo*lo <= x < hi*hi
    return lo, hi


R = F(2271, 10000)
TARGET = F(227, 1000)
assert TARGET < R < F(1, 2) and 5*R*R < 1
# At most 13 owned arcs would have combined half-angle below pi:
# sin(pi/13)>R, hence 13 asin(R)<pi.  sin is increasing here.
x = PI_LO/13
assert x-x**3/6 > R

SQRT3_HI = root_bounds(F(3))[1]
triangle_bound = 3*SQRT3_HI*R*R/4
rows = []
for owners in range(14, 27):
    lo, hi = PI_LO/owners, PI_HI/owners
    # On [0,1] sine increases and cosine decreases.  These rational intervals
    # contain sin(delta), cos(delta) at the true delta=pi/owners.
    sin_lo, sin_hi = sin_bounds(lo)[0], sin_bounds(hi)[1]
    cos_lo, cos_hi = cos_bounds(hi)[0], cos_bounds(lo)[1]
    assert 0 < sin_lo <= sin_hi < R and 0 < cos_lo <= cos_hi < 1
    root_hi = root_bounds(R*R-sin_lo*sin_lo)[1]
    curved_fan_hi = hi - sin_lo*cos_lo + sin_hi*root_hi
    total_hi = ((50-owners)*triangle_bound
                + owners*R*R/2 + owners*curved_fan_hi)
    assert total_hi < PI_LO
    rows.append({"owners": owners,
                 "area_upper": str(total_hi),
                 "strict_gap": str(PI_LO-total_hi),
                 "area_upper_decimal": float(total_hi)})

# A readable coarser summary, also checked with exact comparisons.
assert max(F(row["area_upper"]) for row in rows) < F(313721, 100000)
print(json.dumps({
    "scope": "numerical premises; geometric proof is in AREA-PROOF.md",
    "hypothetical_cover_radius": str(TARGET),
    "generic_enlargement_radius": str(R),
    "pi_bounds": [str(PI_LO), str(PI_HI)],
    "owner_cases": rows,
    "universal_area_upper": "313721/100000",
    "pi_lower": str(PI_LO),
    "passed": True,
}, indent=2))
