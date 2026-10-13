"""R20-W-step0: CALIBRATION of the KKT/affine/sign conventions on toy instances.

Two toys with known answers, used to pin the conventions BEFORE solving the real system:
  T1  f(x) = -(x - 0.3)^2  on  x in [0, 1]   -> maximum at x*=0.3 (interior): f'(x*) = 0
  T2  f(x) = x             on  x in [0, 1]   -> maximum at x*=1 (upper boundary): f'(x*) > 0,
                                                and moving INWARD (dx < 0) must not increase f,
                                                i.e. f'(x*) * dx <= 0 for every dx < 0, hence
                                                f'(x*) >= 0
  T3  f(x) = -x            on  x in [0, 1]   -> maximum at x*=0 (lower boundary): f'(x*) = -1
                                                <= 0 (inward is dx > 0)
  T4  affine system with b(p) != 0: f(p;z) = b(p) + a(p) z, b(p) = -(p-0.3)^2, a(p) = p.
      Stationarity at p*=0.3 must be  b'(p*) + a'(p*) z = 0  ->  -2(0)+1*z = 0 -> z = 0,
      NOT the homogeneous a'(p*) z = 0 which would also be satisfied.
      With b(p) = -(p-0.3)^2 + 2(p-0.3) (derivative +2 at p*): b'+a'z = 2 + z = 0 -> z = -2.
"""
import math
import numpy as np


def t1():
    x = 0.3
    f = lambda t: -(t - 0.3) ** 2
    d = (f(x + 1e-6) - f(x - 1e-6)) / 2e-6
    return dict(interior=True, x=x, fprime=d, ok=abs(d) < 1e-9)


def t2():
    x = 1.0
    f = lambda t: t
    d = (f(x) - f(x - 1e-6)) / 1e-6            # one-sided: inward = dx < 0
    return dict(at_upper=True, x=x, inward_deriv=d, ok=d > 0)


def t3():
    x = 0.0
    f = lambda t: -t
    d = (f(x + 1e-6) - f(x)) / 1e-6            # one-sided: inward = dx > 0
    return dict(at_lower=True, x=x, inward_deriv=d, ok=d < 0)


def t4():
    """affine stationarity test: does the homogeneous rule wrongly admit a solution?"""
    # b(p) = -(p-0.3)^2 + 2(p-0.3),  a(p) = p,  p* = 0.3
    bp = 2.0        # b'(p*)
    ap = 1.0        # a'(p*)
    z_true = -bp / ap      # affine rule  b' + a' z = 0
    z_hom = 0.0            # homogeneous rule a' z = 0
    # evaluate f'(p*) = b' + a' z for both
    return dict(b_prime=bp, a_prime=ap, z_affine=z_true, z_homogeneous=z_hom,
                resid_affine=bp + ap * z_true, resid_homog=bp + ap * z_hom,
                homog_wrong=abs(bp + ap * z_hom) > 1e-12)


if __name__ == '__main__':
    for name, fn in [('T1 interior maximum', t1), ('T2 upper boundary', t2),
                     ('T3 lower boundary', t3), ('T4 affine stationarity', t4)]:
        print('%-24s %s' % (name, fn()))
