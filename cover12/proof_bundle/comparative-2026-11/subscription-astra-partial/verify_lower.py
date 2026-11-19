from functools import lru_cache
from fractions import Fraction
from math import factorial

# R, circle test radii and center radii are in units of 1/1000.
R = 352
M = 100000
# i/50 is the test-circle radius. Each circle has the indicated total mass.
WEIGHTS = {
    17: 1324, 18: 702561, 19: 444828, 20: 407593,
    21: 346446, 22: 299768, 23: 257792, 24: 226664,
    25: 187238, 26: 169135, 27: 113764, 28: 114550,
    29: 5903, 50: 8733755,
}
PI_LO = Fraction(314159, 100000)


def atan_partial(x, terms):
    return sum((-1)**k * x**(2*k+1) / (2*k+1) for k in range(terms))


def check_pi_lo():
    # Machin's identity follows from the tangent addition law.
    a_lo = atan_partial(Fraction(1, 5), 6)
    b_hi = atan_partial(Fraction(1, 239), 3)
    assert 16*a_lo - 4*b_hi > PI_LO


D = PI_LO.denominator * M
COS_DEN = D**16 * factorial(16)
COEF = [(-1)**j * (factorial(16)//factorial(2*j)) * D**(16-2*j)
        for j in range(9)]


@lru_cache(maxsize=None)
def cos_upper_num(k):
    # Upper numerator of cos(k*pi/M) by cos(k*PI_LO/M)
    # and the sixteen-degree upper polynomial for cosine.
    x2 = (k*PI_LO.numerator)**2
    p = COEF[-1]
    for coefficient in reversed(COEF[:-1]):
        p = p*x2 + coefficient
    return p


def radial_units_upper(rad, left, right, radius):
    z = rad*rad - radius*radius
    if left == 0 and z <= 0:
        return M

    if left*left <= z <= right*right:
        # Exact minimum of the cosine is sqrt(z)/rad.
        def enough(q):
            return q <= 0 or (q*rad)**2 <= z*COS_DEN**2
    else:
        center = right if right*right < z else left
        numerator = center*center + z
        denom = 2*center*rad
        assert denom > 0
        if numerator >= denom:
            return 0
        if numerator <= -denom:
            return M

        def enough(q):
            return q*denom <= numerator*COS_DEN

    lo, hi = 0, M
    while hi - lo > 1:
        mid = (lo+hi)//2
        if enough(cos_upper_num(mid)):
            hi = mid
        else:
            lo = mid
    return hi


def check_lower():
    check_pi_lo()
    maximum = -1
    argmax = None
    for left in range(1000):
        score = sum(weight*radial_units_upper(20*i, left, left+1, R) for i, weight in WEIGHTS.items())
        if score > maximum:
            maximum, argmax = score, left
    total = sum(WEIGHTS.values())*M
    assert 12*maximum < total
    print('lower bound > 352/1000 verified using integer/rational arithmetic')
    print('one-disk mass <=',maximum,'/',M,'(left bin',argmax,')')
    print('12-disk mass <=',12*maximum,'/',M,'< total',total,'/',M)


if __name__ == '__main__':
    check_lower()
