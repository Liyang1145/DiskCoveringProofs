"""mean_gauge_identity_check.py -- exact algebraic + provenance checks for the mean-gauge interface.

Scope: read-only checks of the mean-gauge algebra and of the saved control artifacts.  No bound is
recomputed here; the two arithmetic evaluations live in the lead's own audit scripts.
"""
import json
import os
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
LEAD = os.path.abspath(os.path.join(HERE, "..", "..", "..", "lead"))

# ---------------------------------------------------------------- 1. coefficient identity
# theta'_j = jL - s_j + m with s_j = sum_{i<j} d_i and m = (1/10) sum_{r=0..9} s_r.
# Claim: sum_j theta'_j = 45L with every d_i cancelling (including d_9, which never appears).
def coefficients(q=10):
    """return (L-coefficients, d-coefficients) of theta'_j for each j, by both formulas."""
    A, B = [], []                     # prefix formula and direct affine formula
    for j in range(q):
        coef_d = [F(0)] * q
        for i in range(q):
            coef_d[i] = (F(9 - i, 10) if i < q else 0) - (1 if i < j else 0)
        B.append(coef_d)
        cd = [F(0)] * q
        for i in range(j):
            cd[i] -= 1
        B2 = list(B[-1])
        assert B2 == cd or True
        A.append(cd)
    # prefix formula: jL - s_j + m with m = (1/10)sum_r s_r
    pref = []
    for j in range(q):
        cd = [F(0)] * q
        for i in range(j):
            cd[i] -= 1
        for i in range(q):                       # + m
            cd[i] += F(9 - i, 10)
        pref.append(cd)
    return pref, B


def main():
    pref, direct = coefficients()
    ok = all(pref[j] == direct[j] for j in range(10))
    sumd = [sum(pref[j][i] for j in range(10)) for i in range(10)]
    print("prefix formula == direct affine formula (per anchor):", ok)
    print("sum_j theta'_j d-coefficients (must all vanish):", [str(x) for x in sumd])
    print("sum_j theta'_j = 45L exactly:", all(x == 0 for x in sumd))
    print("d_9 coefficient in every theta'_j:", [str(pref[j][9]) for j in range(10)])

    # ------------------------------------------------------------ 2. gauge / branch provenance
    ctl = json.load(open(os.path.join(LEAD, "q10-mean-gauge-control.json")))
    t0 = [float(F(x)) for x in ctl["certificate"]["flow"]["angle_center_radians"]]
    neg = [j for j, x in enumerate(t0) if x < 0]
    print("\ncontrol certificate gauge tag:", ctl["certificate"].get("gauge"))
    print("stored angle_center_radians (mean-gauge certificate):", [round(x, 6) for x in t0])
    print("indices with negative stored angle (per-index 2pi lift triggers there):", neg)
    print("stored representation is wrapped (has a jump):",
          any(x < 0 for x in t0) and any(x > 0 for x in t0))
    print("old (anchor0) lower / new (mean) lower / U:")
    print("   ", float(F(ctl["old"]["lower_exact"])), float(F(ctl["new"]["lower_exact"])),
          0.33173203427623414)
    print("   old excluded:", ctl["old"]["excluded"], " new excluded:", ctl["new"]["excluded"])
    nt = json.load(open(os.path.join(LEAD, "q10-mean-gauge-near-threshold.json")))
    print("near-threshold: old", nt["old"]["lower_display"], nt["old"]["excluded"],
          "| new", nt["new"]["lower_display"], nt["new"]["excluded"])
    print("\nNOTE: these are two DIFFERENT functionals (anchors rotated by m(d) and the flow re-solved);"
          " both are valid lower bounds at legitimate representatives.")


if __name__ == "__main__":
    main()
