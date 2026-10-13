"""n12 -- RIGOROUS finite counting bound for k=11 at radius r (corrected).

NECESSARY CONDITIONS (all proved; no Voronoi, no symmetry, no candidate).

Notation: hub disc B(h,r), e = |h| <= 3r-1 (it must contain B(0,1-2r));
eleven ring discs, every one boundary-active: centre norm t_i >= 1-r.
beta = signed angle measured from the BACKWARD ray w = -h/|h|.  The hub
covers, along the ray beta, exactly the segment [0, R(beta)] with
     R(beta) = -e cos(beta) + sqrt(r^2 - e^2 sin^2(beta)) > 0,
and the ring must reach down to R(beta) on every ray (closedness argument).

(P1) A ring disc of norm t covers an S^1 arc of half-width
     alpha(t) = arccos((1+t^2-r^2)/(2t)) <= asin r; covering S^1 gives
     sum_i alpha_i >= pi.
(P2) Reach criterion.  A ring disc whose centre is at angular distance d from
     the ray beta reaches down to R(beta) at beta iff
       t sin d <= r  and ( R(beta) sin d > r  or  t <= f(R(beta), d) ),
     f(R,d) = R cos d + sqrt(r^2 - R^2 sin^2 d),  f(R,0)=R+r, f decreasing in d.
     In the region R(beta) <= r the escape clause is impossible, hence
        t <= f(R(beta), d) <= R(beta) + r
     and therefore  alpha <= A(beta) := alpha(min(sqrt(1-r^2), R(beta)+r)).
(P3) t >= 1-r and f(R,d) >= 1-r  <=>  d <= dmax(R), so a disc reaching down at
     beta has d <= dmax(R(beta)).  dmax is computed here by bisection and then
     INFLATED by tol, so the arcs [beta +- dmax_up] are supersets: showing them
     pairwise disjoint certifies that the serving discs are DISTINCT.

Hence, for any beta_1..beta_M with pairwise disjoint arcs [beta_m +- dmax_up]:
     sum_i alpha_i <= sum_m A(beta_m) + (11-M) asin r .
If this is < pi, k=11 is impossible at radius r.

Run: py -3 counting_final.py [r] [tol]
"""
import json
import sys
import numpy as np

U = 0.361102963744508672616920293904


def alpha(t, r):
    return np.arccos(np.clip((1.0 + t * t - r * r) / (2.0 * t), -1.0, 1.0))


def R_of(beta, r, e):
    s = np.sin(beta)
    return -e * np.cos(beta) + np.sqrt(np.maximum(0.0, r * r - e * e * s * s))


def f_of(R, d, r):
    return R * np.cos(d) + np.sqrt(np.maximum(0.0, r * r - R * R * np.sin(d) ** 2))


def dmax_up(R, r, lo, tol=1e-9, iters=60):
    """upper bound for max{d>=0 : f(R,d) >= lo}; f is decreasing in d.
    Vectorised over the array R."""
    R = np.asarray(R, float)
    out = np.full(R.shape, -1.0)
    if R.ndim == 0:
        R = R.reshape(1)
        out = out.reshape(1)
    can = R + r >= lo
    dtop = np.where(R > r, np.arcsin(np.minimum(1.0, r / np.maximum(R, 1e-300))),
                    np.pi / 2.0)
    f_top = f_of(R, dtop, r)
    full = can & (f_top >= lo)
    out[full] = dtop[full] + tol
    part = can & ~full
    if np.any(part):
        a = np.zeros_like(R)
        b = dtop.copy()
        for _ in range(iters):
            m = 0.5 * (a + b)
            up = f_of(R, m, r) >= lo
            a = np.where(up, m, a)
            b = np.where(up, b, m)
        out[part] = a[part] + tol
    return out


def pack(r, e, tol=1e-9, ngrid=6001, nmax=11):
    lo, hi = 1.0 - r, np.sqrt(max(0.0, 1.0 - r * r))
    Ainf = float(alpha(hi, r))
    bet = np.linspace(0.0, 2.0 * np.pi, ngrid, endpoint=False)
    R = R_of(bet, r, e)
    good = R <= r + 1e-15
    dm = np.full(ngrid, -1.0)
    idx = np.nonzero(good)[0]
    if len(idx):
        dm[idx] = dmax_up(R[idx], r, lo, tol)
    A = alpha(np.minimum(hi, R + r), r)
    picks, cur = [], 0.0
    for _ in range(nmax):
        found = None
        for step in range(0, ngrid):
            for sgn in ((1, -1) if step else (1,)):
                j = (sgn * step) % ngrid
                if dm[j] < 0:
                    continue
                b = bet[j] if sgn > 0 else bet[j] - 2.0 * np.pi
                if b - dm[j] >= cur:
                    found = (j, b + dm[j])
                    break
            if found:
                break
        if found is None:
            break
        picks.append(found[0])
        cur = found[1]
    # explicit disjointness verification of the inflated arcs on the circle
    arcs = []
    for j in picks:
        b = float(bet[j])
        arcs.append(((b - dm[j]) % (2 * np.pi), (b + dm[j]) % (2 * np.pi)))
    ok = True
    for i in range(len(picks)):
        for k in range(len(picks)):
            if i == k:
                continue
            bi = float(bet[picks[i]])
            ai = dm[picks[i]]
            bk = float(bet[picks[k]])
            ak = dm[picks[k]]
            dd = abs((bi - bk + np.pi) % (2 * np.pi) - np.pi)
            if dd <= ai + ak:
                ok = False
    return picks, bet, R, A, Ainf, ok, dm


def bound_table(r, e, tol=1e-9):
    picks, bet, R, A, Ainf, ok, dm = pack(r, e, tol)
    rows = []
    for M in range(1, len(picks) + 1):
        s = float(np.sum(A[picks[:M]]))
        rows.append(dict(M=M, bound_deg=float(np.degrees(s + (11 - M) * Ainf)),
                         sum_A=float(np.degrees(s)),
                         betas=[round(float(np.degrees(bet[i])), 3)
                                for i in picks[:M]],
                         dmax=[round(float(np.degrees(dm[i])), 3)
                               for i in picks[:M]],
                         As=[round(float(np.degrees(A[i])), 3)
                             for i in picks[:M]]))
    return rows, Ainf, ok, len(picks)


def capacity_rows(r, e):
    lo, hi = 1.0 - r, np.sqrt(max(0.0, 1.0 - r * r))
    Ainf = float(alpha(hi, r))
    Bmax = float(np.arccos(min(1.0, (1.0 - r - e) / (2.0 * r))))
    nmin = int(np.ceil(np.pi / Bmax))
    rows = []
    for n in range(nmin, 12):
        B = np.pi / n
        t = min(hi, 2.0 * r * np.cos(B) + e)
        rows.append((n, float(np.degrees(n * float(alpha(t, r))
                                         + (11 - n) * Ainf))))
    return rows, Bmax, nmin


def main():
    r = float(sys.argv[1]) if len(sys.argv) > 1 else U
    tol = float(sys.argv[2]) if len(sys.argv) > 2 else 1e-9
    print("r = %.18f   asin r = %.6f deg   tol=%.1e"
          % (r, np.degrees(np.arcsin(r)), tol))
    print("    e        count_min  M*  (Mmax)   cap_max  n*   verdict")
    res = {}
    for e in [0.0, 0.005, 0.01, 0.015, 0.02, 0.025, 0.03, 0.035, 0.04,
              0.045, 0.05, 0.055, 0.06, 0.065, 0.07, 0.075, 0.08,
              3.0 * r - 1.0]:
        rows, Ainf, ok, nmax = bound_table(r, e, tol)
        cm = min(rows, key=lambda z: z["bound_deg"])
        cap, Bmax, nmin = capacity_rows(r, e)
        cp = max(cap, key=lambda z: z[1])
        verdict = []
        if cm["bound_deg"] < 180.0 and ok:
            verdict.append("COUNT")
        if cp[1] < 180.0:
            verdict.append("CAP")
        print("  %.5f   %9.3f  %2d  (%2d)  %9.3f  %2d   %s"
              % (e, cm["bound_deg"], cm["M"], nmax, cp[1], cp[0],
                 "+".join(verdict) if verdict else "-- none --"), flush=True)
        res["%.5f" % e] = dict(count_best=cm, count_max_M=nmax,
                               count_arcs_disjoint=ok,
                               capacity_best=dict(n=cp[0], bound=cp[1]),
                               Bmax_deg=float(np.degrees(Bmax)), nmin=nmin,
                               Ainf_deg=float(np.degrees(Ainf)))
    json.dump(res, open("counting_final_out.json", "w"), indent=1)


if __name__ == "__main__":
    main()
