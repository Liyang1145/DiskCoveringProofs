"""Run all the finite arithmetic checks used in the proof."""
from fractions import Fraction
from exclude11 import certify_boundary_count
from grid_exact import center_key, series_term
from local import certify_local_inequalities
from lower3545 import certify_lower_bound
from symmetric import certify_symmetric_root
from upper import certify_upper


def arctan_interval(q):
    x = Fraction(1, q)
    lo = sum((-1)**k*x**(2*k+1)/(2*k+1) for k in range(8))
    return lo, lo + x**17/17


def verify_pi_bounds():
    a, b = arctan_interval(5)
    c, d = arctan_interval(239)
    assert Fraction("3.14159") < 16*a-4*d
    assert 16*b-4*c < Fraction("3.14160")


def verify_outer_separation():
    r = Fraction(".361103")
    t, phi = Fraction(".70"), Fraction(".242")
    assert (1+t*t-r*r)/(2*t) > 1-phi**2/2+phi**4/24
    x, y = Fraction("1.10318")/2, Fraction("1.23118")/2
    assert 2*t*(x-x**3/6) > 2*r
    assert 2*(1-r)*(y-y**3/6) > 2*r


if __name__ == "__main__":
    verify_pi_bounds()
    verify_outer_separation()
    certify_lower_bound()
    certify_boundary_count()
    certify_upper()
    certify_symmetric_root()
    certify_local_inequalities()
    assert tuple(series_term(k) for k in range(4)) == (1, 1, 1, 3)
    assert center_key(0, 1) == center_key(1, 1) == 0
