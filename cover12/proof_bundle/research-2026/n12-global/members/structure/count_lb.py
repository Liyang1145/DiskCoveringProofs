"""n12 -- finite counting lower bound for k=11 at radius r.

Necessary conditions used (all proved in the note; see reach.py):
  * every boundary-active centre has norm t_i in [1-r, 1+r] and its disc
    covers an arc of S^1 of half-width alpha_i = arccos((1+t_i^2-r^2)/(2t_i))
    <= asin r;  covering S^1 forces  sum_i alpha_i >= pi.
  * hub disc B(h,r) with e=|h| covers, along the ray at signed angle beta
    from the BACKWARD ray, the segment [0, R(beta)],
       R(beta) = -e cos beta + sqrt(r^2 - e^2 sin^2 beta),
    and the ring must reach down to R(beta) on every ray.
  * if beta has R(beta) <= r (so the "far disk" escape cannot apply), then any
    ring disc that reaches down to R(beta) at beta must have
       |gamma - beta| <= dmax(beta)   and   alpha <= A(beta),
       dmax(beta) = max{d : f(R(beta),d) >= 1-r},
       A(beta)    = alpha(min(sqrt(1-r^2), R(beta)+r)),
       f(R,d)     = R cos d + sqrt(r^2 - R^2 sin^2 d).
Hence for any beta_1..beta_M with pairwise disjoint arcs I_m = [beta_m +-
dmax(beta_m)], the M serving discs are DISTINCT, so

       sum_i alpha_i  <=  sum_m A(beta_m) + (11-M) asin r .

If that upper bound is < pi, k=11 is impossible at radius r.
Everything is a finite check on a 1-D grid.

Run: py -3 count_lb.py [r]
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


def dmax(R, r, lo):
    """max d with f(R,d) >= lo, or None if impossible."""
    if R + r < lo:
        return None
    f0 = R * r * 0.0 + R + r
    if f0 < lo:
        return None
    hi = np.pi / 2.0
    # f decreasing in d on [0, arcsin(r/R)] (or on [0,pi/2] when R<=r)
    d = np.linspace(0.0, np.pi / 2.0, 200001)
    Rs = R * np.sin(d)
    f = R * np.cos(d) + np.sqrt(np.maximum(0.0, r * r - R * R * np.sin(d) ** 2))
    ok = f >= lo
    idx = np.nonzero(~ok)[0]
    if len(idx) == 0:
        return float(np.pi / 2.0)
    return float(d[idx[0] - 1]) if idx[0] > 0 else 0.0


def bound_for_e(r, e, nbeta=200001, nmax=11, verbose=False):
    lo = 1.0 - r
    hi = np.sqrt(max(0.0, 1.0 - r * r))
    Asin = float(alpha(hi, r))                      # asin r
    bet = np.linspace(0.0, np.pi, nbeta)
    R = R_of(bet, r, e)
    good = R <= r + 1e-15                           # far-disc escape impossible
    # dmax and A on a coarse grid (cheap), refine greedily when packing
    ngrid = 4000
    bs = np.linspace(0.0, np.pi, ngrid)
    Rs = R_of(bs, r, e)
    dm = np.array([dmax(float(Rv), r, lo) if Rv <= r + 1e-15 else np.nan
                   for Rv in Rs])
    tmax = np.minimum(hi, Rs + r)
    Am = alpha(tmax, r)
    # greedy packing of disjoint [b-dmax, b+dmax], b in [0, pi]
    picks = []
    cur = 0.0
    for _ in range(nmax):
        # smallest b >= cur with b - dmax(b) >= cur
        cand = None
        for i in range(ngrid):
            b = bs[i]
            if b < cur:
                continue
            if not np.isfinite(dm[i]):
                break
            if b - dm[i] >= cur - 1e-12:
                cand = i
                break
        if cand is None:
            break
        picks.append(cand)
        cur = bs[cand] + dm[cand]
    rows = []
    for M in range(1, len(picks) + 1):
        s = float(np.sum(Am[picks[:M]]))
        bd = s + (11 - M) * Asin
        rows.append(dict(M=M, sumA=float(np.degrees(s)),
                         bound_deg=float(np.degrees(bd)),
                         betas=[round(float(np.degrees(bs[i])), 4)
                                for i in picks[:M]]))
    return Asin, rows, picks


def main():
    r = float(sys.argv[1]) if len(sys.argv) > 1 else U
    print("r = %.18f   (asin r = %.6f deg, pi = 180 deg)"
          % (r, np.degrees(np.arcsin(r))))
    out = {}
    for e in [0.0, 0.01, 0.02, 0.03, 0.04, 0.05, 0.06, 0.07,
              3.0 * r - 1.0]:
        Asin, rows, picks = bound_for_e(r, e)
        best = min(rows, key=lambda z: z["bound_deg"]) if rows else None
        tag = "CONTRADICTION" if best and best["bound_deg"] < 180.0 else "-"
        print("  e=%.6f  M*=%d  bound=%.3f deg  %s" %
              (e, best["M"] if best else 0,
               best["bound_deg"] if best else float("nan"), tag), flush=True)
        out["e=%.6f" % e] = dict(best=best, asin_deg=float(np.degrees(Asin)))
    json.dump(out, open("count_lb_out.json", "w"), indent=1)


if __name__ == "__main__":
    main()
