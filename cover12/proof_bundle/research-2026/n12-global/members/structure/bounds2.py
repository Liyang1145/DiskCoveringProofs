"""n12 -- two complementary finite lower bounds for k=11 at radius r.

(L1) CAPACITY (two circles S^1 and S(h,r)).
  Deep discs are those with s_i = |c_i-h| <= 2r; only they can meet the hub
  boundary circle S(h,r); they cover it in arcs of half-width
  B_i = arccos(s_i/(2r)), so  sum_{deep} B_i >= pi.  Writing s_i = 2r cos B_i
  and t_i <= s_i + e (best alignment), the S^1 arc obeys
  alpha_i <= h_e(B_i) := alpha(2r cos B_i + e); h_e is concave, so Jensen
  gives  sum_{deep} alpha_i <= n h_e(pi/n)  with n = #{deep} >= pi/B_max,
  B_max = arccos((1-r-e)/(2r)).  Remaining discs have alpha <= asin r.  Hence
     sum_i alpha_i <= n h_e(pi/n) + (11-n) asin r  for every admissible n.

(L2) COUNTING (per-ray reach neighbourhoods).
  For beta with R(beta) <= r only the "good regime" is available, so any disc
  reaching down to R(beta) at beta has centre within dmax(beta) of beta and
  alpha <= A(beta) = alpha(R(beta)+r).  M directions with pairwise disjoint
  arcs [beta +- dmax(beta)] therefore need M DISTINCT discs, giving
     sum_i alpha_i <= sum_m A(beta_m) + (11-M) asin r .

Both are necessary; whichever drops below pi excludes k=11 at radius r.
Script reports min over the free parameters of each bound.

Run: py -3 bounds2.py [r]
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
    if R + r < lo:
        return None
    d = np.linspace(0.0, np.pi / 2.0, 400001)
    f = R * np.cos(d) + np.sqrt(np.maximum(0.0, r * r - R * R * np.sin(d) ** 2))
    ok = f >= lo
    idx = np.nonzero(~ok)[0]
    if len(idx) == 0:
        return float(np.pi / 2.0)
    return float(d[idx[0] - 1]) if idx[0] > 0 else 0.0


def capacity_bound(r, e, verbose=False):
    lo = 1.0 - r
    hi = np.sqrt(max(0.0, 1.0 - r * r))
    A = float(alpha(hi, r))
    Bmax = float(np.arccos((1.0 - r - e) / (2.0 * r))) if (1.0 - r - e) <= 2.0 * r else 0.0
    if Bmax <= 0.0:
        nmin = 11
    else:
        nmin = int(np.ceil(np.pi / Bmax))
    rows = []
    for n in range(max(nmin, 1), 12):
        Bn = np.pi / n
        h = float(alpha(min(hi, 2.0 * r * np.cos(Bn) + e), r))
        rows.append((n, float(np.degrees(n * h + (11 - n) * A))))
    return rows


def count_bound(r, e, ngrid=6000, nmax=11):
    lo = 1.0 - r
    hi = np.sqrt(max(0.0, 1.0 - r * r))
    Ainf = float(alpha(hi, r))
    bet = np.linspace(0.0, 2.0 * np.pi, ngrid, endpoint=False)
    R = R_of(bet, r, e)
    ok_good = R <= r + 1e-12
    tmax = np.minimum(hi, R + r)
    A = alpha(tmax, r)
    dm = np.full(ngrid, -1.0)
    for i in np.nonzero(ok_good)[0]:
        d = dmax(float(R[i]), r, lo)
        dm[i] = d if d is not None else -1.0
    # greedy packing on the circle, starting at beta=0, strict progress
    picks = []
    cur = 0.0
    eps = 1e-9
    for _ in range(nmax):
        cand = None
        # walk outward from beta=0 in both directions
        for step in range(1, ngrid):
            for sgn in (1, -1):
                j = (0 + sgn * step) % ngrid
                if dm[j] < 0:
                    continue
                b = bet[j] if sgn > 0 else (bet[j] - 2 * np.pi)
                if b - dm[j] >= cur - 1e-12:
                    cand = (j, b + dm[j] + eps)
                    break
            if cand:
                break
        if cand is None:
            break
        picks.append(cand[0])
        cur = cand[1]
    rows = []
    for M in range(1, len(picks) + 1):
        s = float(np.sum(A[picks[:M]]))
        rows.append((M, float(np.degrees(s + (11 - M) * Ainf)),
                     [round(float(np.degrees(bet[i])), 3) for i in picks[:M]]))
    return rows, Ainf


def main():
    r = float(sys.argv[1]) if len(sys.argv) > 1 else U
    print("r = %.18f  (asin r = %.6f deg)" % (r, np.degrees(np.arcsin(r))))
    print(" e        cap_min(deg)  n*   count_min(deg)  M*    verdict")
    out = {}
    for e in [0.0, 0.01, 0.02, 0.03, 0.04, 0.05, 0.06, 0.065, 0.07,
              0.075, 0.08, 3.0 * r - 1.0]:
        cap = capacity_bound(r, e)
        cnt, Ainf = count_bound(r, e)
        cm = min(cap, key=lambda z: z[1]) if cap else None
        km = min(cnt, key=lambda z: z[1]) if cnt else None
        v = []
        if cm and cm[1] < 180.0:
            v.append("CAP")
        if km and km[1] < 180.0:
            v.append("COUNT")
        print(" %.5f  %10.3f  %2d  %10.3f  %2d   %s" %
              (e, cm[1] if cm else float("nan"), cm[0] if cm else 0,
               km[1] if km else float("nan"), km[0] if km else 0,
               "EXCLUDES(k=11)" if v else "no contradiction"))
        out["%.5f" % e] = dict(capacity=cm, counting=km)
    json.dump(out, open("bounds2_out.json", "w"), indent=1)


if __name__ == "__main__":
    main()
