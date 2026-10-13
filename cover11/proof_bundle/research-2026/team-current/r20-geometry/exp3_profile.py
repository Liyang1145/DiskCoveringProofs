"""Profile scan of the general seven-factor objective (evaluation-only, deterministic grids).

The "everything else fixed" sweep is infeasible because the certified cover sits on the
face-circumradius boundary (A,H are pinned).  So each slice re-maximises over the legal
(A,H) rectangle by a deterministic grid + refinement (no multistart optimiser is used).

Slices:
  (A) symmetric profile alpha2 = pi ... 0.0233 at the candidate's outer data
  (B) asymmetric s1 != s2 and alpha1 != alpha3 variations at the candidate's alpha2
  (C) degenerate corners
"""
import json, math, sys, itertools
from pathlib import Path
import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import r20_lib as L

PI, R, TAU = L.PI, L.R, L.TAU
d0 = json.load(open(HERE / "cand_local_data.json"))
t = d0["t"]
THRESH = 28.10704541577262956809
CERT_HB = 28.106948822740861261
NUM_FLAT = 28.104237014746577
J_CAND = 28.114478844683

OUT = []


def profile_J(base, nA=48, nH=48, refine=3):
    """max J over the legal (A,H) rectangle for the given base parameter dict."""
    p = dict(base)
    best = (-1e18, None)
    # outer rectangle: A in (0, Theta), H in (0.02, 2R); Theta from closure
    bb = L.closure_b(p)
    if bb is None:
        return None
    b1, b2 = bb
    Theta = PI + b1 + b2 - p["a2"]
    if Theta <= 0:
        return None
    Alo, Ahi = 1e-3 * Theta, (1 - 1e-3) * Theta
    Hlo, Hhi = 0.02, 2 * R
    counts = 0
    for it in range(refine):
        As = np.linspace(Alo, Ahi, nA)
        Hs = np.linspace(Hlo, Hhi, nH)
        for A in As:
            for H in Hs:
                q = dict(p, A=float(A), H=float(H))
                g = L.gen_args(q)
                if g is None:
                    continue
                counts += 1
                if min(L.gen_margins(q, g)[1]) < -1e-9:
                    continue
                J = L.gen_value(g)
                if J > best[0]:
                    best = (J, (A, H, g))
        if best[1] is None:
            return None
        A0, H0, _ = best[1]
        dA = (Ahi - Alo) / nA
        dH = (Hhi - Hlo) / nH
        Alo, Ahi = A0 - dA, A0 + dA
        Hlo, Hhi = H0 - dH, H0 + dH
    return dict(J=best[0], A=best[1][0], H=best[1][1], evals=counts)


print("== (A) symmetric profile: alpha2 sweep at the candidate's outer data ==")
print("   alpha2      pi-alpha2   J_profile      A          H        evals   vs threshold")
base = dict(t=t, a1=d0["a1"], u1=d0["u1"], s1=t, a2=d0["a2"], s2=t, a3=d0["a3"], v3=d0["v3"],
            A=d0["A"], H=d0["H"])
for a2 in [PI, PI - 0.005, PI - 0.02, PI - 0.05, PI - 0.10, d0["a2"], PI - 0.25, PI - 0.4, PI - 0.6, 0.1]:
    b = dict(base, a2=float(a2))
    r = profile_J(b)
    if r is None:
        print("   %9.6f   %8.6f   infeasible" % (a2, PI - a2))
        continue
    print("   %9.6f   %8.6f   %12.8f  %8.6f  %8.6f  %6d   %+.4e"
          % (a2, PI - a2, r["J"], r["A"], r["H"], r["evals"], r["J"] - THRESH))
    OUT.append(dict(kind="profile", a2=float(a2), J=r["J"], A=r["A"], H=r["H"]))

print("\n== (B) asymmetric checks at the candidate's alpha2 ==")
print("   ds1     ds2     dalpha1  dalpha3   J          legal   (offset vs J_cand)")
best_asym = (-1e18, None)
for ds1, ds2 in [(0.0, 0.0), (0.005, 0.0), (0.0, 0.005), (0.02, 0.0), (0.0, 0.02), (0.05, 0.02), (0.1, 0.1)]:
    for da1, da3 in [(0.0, 0.0), (0.05, 0.0), (0.0, 0.05), (0.1, -0.1)]:
        b = dict(base, s1=max(0.05, t - ds1), s2=max(0.05, t - ds2),
                 a1=d0["a1"] + da1, a3=d0["a3"] + da3)
        r = profile_J(b, nA=24, nH=24, refine=2)
        if r is None:
            continue
        if r["J"] > best_asym[0]:
            best_asym = (r["J"], (ds1, ds2, da1, da3, r))
        print("   %6.3f  %6.3f  %+6.3f  %+6.3f   %12.8f          %+.4e"
              % (ds1, ds2, da1, da3, r["J"], r["J"] - J_CAND))
print("   best asymmetric J = %.9f at %s" % (best_asym[0], best_asym[1][:4]))
OUT.append(dict(kind="asym_best", J=best_asym[0], params=best_asym[1][:4]))

print("\n== (C) degenerate corners ==")
for tag, b in [("alpha2->floor(0.0233)", dict(base, a2=0.0233)),
               ("s1=s2=0.05", dict(base, s1=0.05, s2=0.05)),
               ("s1=s2=0.5", dict(base, s1=0.5, s2=0.5)),
               ("flat + s=0.9", dict(base, a2=PI, s1=0.9, s2=0.9))]:
    r = profile_J(b, nA=24, nH=24, refine=2)
    print("   %-22s J=%s" % (tag, ("%.9f" % r["J"]) if r else "infeasible"))
    if r:
        OUT.append(dict(kind="degen", tag=tag, J=r["J"]))

print("\nreference values:  J(certified cover) = %.9f ; threshold T = %.9f" % (J_CAND, THRESH))
json.dump(OUT, open(HERE / "exp3_profile.json", "w"), indent=1)
print("wrote exp3_profile.json")
