"""r20-geometry exp5: asymmetric + degenerate attack on the nonflat patch domain.

Target proposition (attacked here):
  Q-Deform:  every legal nonflat patch p of the C849 general chart (alpha2 < pi) admits a
             legal FLAT patch p~ (alpha2 = pi, same chart) with J(p~) >= J(p),
  Q-Cert:    every legal nonflat p has J(p) <= T = 28.10704541577262956809
             (the threshold the current 22-factor certificate leaves for the seven-factor part).

Counterexample already in hand (verify_indep_candidate.py / cand_full29.py):
  p* = the CERTIFIED extremal n11 cover's own patch data.  J(p*) = 28.114478844683 > T.
  The certified flat high-bearing upper bound is 28.1069488227408613 < J(p*).

This script attacks the two propositions with (a) asymmetric switch distances s1 != s2,
(b) asymmetric neighbouring sectors (alpha1, alpha3) and outer endpoints (u1, v3),
(c) degenerate corners (t at its lower end 75/76, alpha_i at the compact-domain floor,
    endpoint distances at the frozen lower bound .19, s -> small), and
(d) a coarse (pi-alpha2) x (s1,s2) box scan for the largest nonflat J we can reach.

All maximizations are DETERMINISTIC grids + nested box refinement over the legal (A,H) fibre:
no random restarts, no multistart optimizer.  Grid values are LOWER bounds on the true fibre
maxima, so "J > T" readings are witnesses while "J < T" readings are only diagnostics.
"""
import json, hashlib, sys
from pathlib import Path
from mpmath import mp, mpf, sin, cos, asin, atan2, sqrt, pi as MP_PI

mp.dps = 30
HERE = Path(__file__).resolve().parent
LEAD = HERE.parent / "lead"
SRC = (HERE / "verify_indep_candidate.py").read_text(encoding="utf-8").split("names, mg = margins(p0)")[0]
G = {"__file__": str(HERE / "verify_indep_candidate.py"), "__name__": "exp5"}
exec(compile(SRC, "verify_indep_candidate", "exec"), G)
mpf_ = G["mpf"]; chart_parts = G["chart_parts"]; margins = G["margins"]; p0 = dict(G["p0"])
seven = G["seven_from_params"]
THRESH = mpf("28.10704541577262956809")
FLAT_HB = mpf("28.1069488227408612601720960810780525207519531")
TOL = mpf("1e-12")


def fiber_max(pp, nA=33, nH=33, refine=3):
    g = chart_parts(pp)
    if g is None:
        return None
    Th = MP_PI + g["b1"] + g["b2"] - pp["a2"]
    Alo, Ahi = Th / 1000, Th * mpf("0.999")
    Hlo, Hhi = mpf("0.02"), 2 * mpf(19) / 50
    best = (None, None)
    for _ in range(refine):
        dA = (Ahi - Alo) / nA
        dH = (Hhi - Hlo) / nH
        for i in range(nA + 1):
            A = Alo + (Ahi - Alo) * mpf(i) / nA
            for j in range(nH + 1):
                H = Hlo + (Hhi - Hlo) * mpf(j) / nH
                q = dict(pp, A=A, H=H)
                mm = margins(q)
                if mm is None or min(mm[1]) < -TOL:
                    continue
                Jv = seven(q)
                if Jv is None:
                    continue
                if best[0] is None or Jv > best[0]:
                    best = (Jv, (A, H))
        if best[1] is None:
            return None
        A0, H0 = best[1]
        Alo, Ahi = A0 - dA, A0 + dA
        Hlo, Hhi = H0 - dH, H0 + dH
    return best


t = p0["t"]
rows = []


def rep(tag, pp, note=""):
    r = fiber_max(pp)
    if r is None:
        print("  %-46s infeasible" % tag)
        rows.append(dict(tag=tag, J=None, note=note))
        return None
    print("  %-46s J=%.12f  J-T=%+.5e  J-FLATHB=%+.5e  %s"
          % (tag, float(r[0]), float(r[0] - THRESH), float(r[0] - FLAT_HB), note))
    rows.append(dict(tag=tag, J=float(r[0]), A=float(r[1][0]), H=float(r[1][1]),
                     J_minus_T=float(r[0] - THRESH), note=note))
    return r


print("=== (0) reference: candidate alpha2, candidate outer data ===")
rep("alpha2=2.967354 (candidate)", p0, "the witness point p*")
base_flat = dict(p0, a2=MP_PI)
rep("alpha2=pi (same outer data)", base_flat, "flat sibling of p*")

print("\n=== (A) asymmetric switch distances (s1 != s2), alpha2 = candidate's ===")
for ds1, ds2 in [(0, 0), (0.005, 0), (0, 0.005), (0.02, 0), (0, 0.02), (0.05, 0.02),
                 (0.1, 0.1), (0.1, 0), (0, 0.1), (0.15, 0.05)]:
    q = dict(p0, s1=t - ds1, s2=t - ds2)
    rep("s1=t-%.3f s2=t-%.3f" % (ds1, ds2), q)

print("\n=== (B) asymmetric neighbours / outer endpoints (alpha2 = candidate's) ===")
for da1, da3 in [(0, 0), (0.1, -0.1), (-0.1, 0.1), (0.3, 0), (0, 0.3), (-0.3, -0.3), (0.6, 0.0)]:
    q = dict(p0, a1=p0["a1"] + da1, a3=p0["a3"] + da3)
    rep("alpha1%+.2f alpha3%+.2f" % (da1, da3), q)
for du1, dv3 in [(0, 0), (0.1, 0), (0, 0.1), (0.3, 0.3), (-0.1, -0.1), (-0.3, 0.0)]:
    q = dict(p0, u1=max(mpf("0.05"), p0["u1"] + du1), v3=max(mpf("0.05"), p0["v3"] + dv3))
    rep("du1%+.2f dv3%+.2f" % (du1, dv3), q)

print("\n=== (C) degenerate corners ===")
rep("t=75/76 (r=.375), alpha2=candidate", dict(p0, t=mpf(75) / 76))
rep("t=75/76, alpha2=pi", dict(p0, t=mpf(75) / 76, a2=MP_PI))
rep("s1=s2=t-0.3", dict(p0, s1=t - mpf("0.3"), s2=t - mpf("0.3")))
rep("u1=v3=0.19", dict(p0, u1=mpf("0.19"), v3=mpf("0.19")))
rep("alpha1=alpha3=pi-1e-6", dict(p0, a1=MP_PI - mpf("1e-6"), a3=MP_PI - mpf("1e-6")))
rep("alpha1=alpha3=0.05", dict(p0, a1=mpf("0.05"), a3=mpf("0.05")))
rep("alpha2 -> floor 0.0233", dict(p0, a2=mpf("0.0233")))
rep("alpha2 = pi-1e-8 (near flat)", dict(p0, a2=MP_PI - mpf("1e-8")))

print("\n=== (D) (pi-alpha2) x (s1,s2) box scan: how high can the nonflat J get? ===")
best = (None, None)
for eps in [mpf("0.15"), mpf("0.3"), mpf("0.45"), mpf("0.6"), mpf("0.8"), mpf("1.0")]:
    for ds1, ds2 in [(0, 0), (0, 0.05), (0.05, 0), (0.1, 0.1)]:
        tag = "pi-a2=%.2f ds1=%.2f ds2=%.2f" % (float(eps), ds1, ds2)
        q = dict(p0, a2=MP_PI - eps, s1=t - mpf(str(ds1)), s2=t - mpf(str(ds2)))
        r = rep(tag, q)
        if r is not None and (best[0] is None or r[0] > best[0]):
            best = (r[0], tag)
print("\nbest nonflat J reached by (D): %.12f  at %s   (T = %.12f, flat high-bearing ub = %.13f)"
      % (float(best[0]), best[1], float(THRESH), float(FLAT_HB)))
print("excess over T       = %+.6e" % float(best[0] - THRESH))
print("excess over flat HB = %+.6e" % float(best[0] - FLAT_HB))

json.dump(dict(threshold=float(THRESH), flat_highbearing_ub=float(FLAT_HB),
               J_candidate_patch=float(G["J"]), rows=rows, best_nonflat=[float(best[0]), best[1]]),
          open(HERE / "exp5_asym_degeneracy.json", "w"), indent=1)
print("\nwrote exp5_asym_degeneracy.json")
