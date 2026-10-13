# -*- coding: utf-8 -*-
"""o1_rbisect.py -- for which r does the m=0 (third disk = k+2) relaxation still admit a
negative O1 margin?  Bisection on r with the multistart minimiser from o1_triple2.
Numeric only.
"""
import importlib.util, math, os, sys
spec = importlib.util.spec_from_file_location("o1t", os.path.join(os.path.dirname(os.path.abspath(__file__)), "o1_triple2.py"))
o1t = importlib.util.module_from_spec(spec)
spec.loader.exec_module(o1t)


def minm(r, nstart=220):
    b = o1t.part1(r, 0, nstart=nstart, seed=7)
    return None if b is None else b[0]


if __name__ == "__main__":
    lo, hi = 0.3709, 0.38
    print("m=0 (third disk = k+2) min margin over the 5D relaxation")
    for r in (0.3709, 0.372, 0.374, 0.376, 0.378, 0.3799, 0.38):
        m = minm(r)
        print("   r=%.4f  min margin = %+.6e" % (r, m))
    for _ in range(7):
        mid = 0.5 * (lo + hi)
        m = minm(mid)
        print("   bisect r=%.6f  min margin = %+.6e" % (mid, m))
        if m < 0:
            hi = mid
        else:
            lo = mid
    print("negative-margin r threshold in [%.6f, %.6f]" % (lo, hi))
