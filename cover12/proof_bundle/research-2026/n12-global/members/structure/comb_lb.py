"""n12 -- combined finite bound for k=11 at r = U (capacity + counting).

Ingredients (see bounds2.py / note for proofs):
 L1 capacity : n = #discs with |c_i-h| <= 2r; sum_{D} B_i >= pi,
               alpha_i <= h_e(B_i), h_e(B) = alpha(min(sqrt(1-r^2), 2r cos B + e));
               Jensen  => sum_D alpha_i <= n h_e(pi/n)  (h_e concave).
 L2 counting : M distinct discs serve M directions beta_m with disjoint arcs
               [beta_m +- dmax(beta_m)]; each has t <= t_m = R(beta_m)+r and
               alpha <= A_m = alpha(t_m).
 Combined    : j of the M serving discs may lie in D (they then supply at most
               B_m = B(t_m) each); the other n-j supply at most B_max each.
               sum alpha <= M Amax + (n-j) h_e((pi - j Bm)/(n-j)) + (11-n) asin r.

The script maximises each bound over its free discrete parameters and reports
the MINIMUM over M (all packings give valid bounds simultaneously).

Run: py -3 comb_lb.py [r]
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


def dmax(R, r, lo, n=400001):
    if R + r < lo:
        return None
    d = np.linspace(0.0, np.pi / 2.0, n)
    f = R * np.cos(d) + np.sqrt(np.maximum(0.0, r * r - R * R * np.sin(d) ** 2))
    ok = f >= lo
    idx = np.nonzero(~ok)[0]
    if len(idx) == 0:
        return float(np.pi / 2.0)
    return float(d[idx[0] - 1]) if idx[0] > 0 else 0.0


def pack(r, e, nmax=11, ngrid=8000):
    """greedy disjoint packing of reach-neighbourhoods; returns
       list of (beta, dmax, A, t) and asin r."""
    lo, hi = 1.0 - r, np.sqrt(max(0.0, 1.0 - r * r))
    Ainf = float(alpha(hi, r))
    bet = np.linspace(0.0, 2.0 * np.pi, ngrid, endpoint=False)
    R = R_of(bet, r, e)
    good = R <= r + 1e-12
    dm = np.full(ngrid, -1.0)
    for i in np.nonzero(good)[0]:
        d = dmax(float(R[i]), r, lo)
        if d is not None:
            dm[i] = d
    picks, cur, eps = [], 0.0, 1e-9
    for _ in range(nmax):
        found = None
        for step in range(0, ngrid):
            for sgn in ((1, -1) if step else (1,)):
                j = (sgn * step) % ngrid
                if dm[j] < 0:
                    continue
                b = bet[j] if sgn > 0 else bet[j] - 2 * np.pi
                if b - dm[j] >= cur - 1e-12:
                    found = (j, b + dm[j] + eps)
                    break
            if found:
                break
        if found is None:
            break
        picks.append(found[0])
        cur = found[1]
    out = []
    for j in picks:
        Rj = float(R[j])
        tj = min(hi, Rj + r)
        out.append(dict(beta=float(np.degrees(bet[j])), R=Rj, t=tj,
                        A=float(np.degrees(alpha(tj, r))),
                        dmax=float(np.degrees(dm[j]))))
    return out, Ainf


def concavity_check(r, e, nb=2001):
    lo, hi = 1.0 - r, np.sqrt(max(0.0, 1.0 - r * r))
    Bmax = np.arccos(min(1.0, (1.0 - r - e) / (2.0 * r)))
    B = np.linspace(1e-6, Bmax, nb)
    h = alpha(np.minimum(hi, 2.0 * r * np.cos(B) + e), r)
    d = B[1] - B[0]
    h2 = (h[2:] - 2 * h[1:-1] + h[:-2]) / d ** 2
    return Bmax, float(h2.max())


def combined(r, e, verbose=False):
    lo, hi = 1.0 - r, np.sqrt(max(0.0, 1.0 - r * r))
    Ainf = float(alpha(hi, r))
    picks, _ = pack(r, e)
    if not picks:
        return None
    Bmax = float(np.arccos(min(1.0, (1.0 - r - e) / (2.0 * r))))
    Bmaxd = float(np.degrees(Bmax))
    nmin = int(np.ceil(np.pi / Bmax))
    def h(Bdeg):                       # h_e at half-width B (degrees)
        B = np.radians(Bdeg)
        return float(np.degrees(alpha(min(hi, 2.0 * r * np.cos(B) + e), r)))
    rows = []
    for M in range(1, len(picks) + 1):
        Am = float(np.sum([p["A"] for p in picks[:M]]))
        tm = max(p["t"] for p in picks[:M])
        Bm = float(np.degrees(np.arccos(min(1.0, max(0.0, tm - e) / (2.0 * r)))))
        best, bestinfo = -1.0, None
        for j in range(0, M + 1):                    # j serving discs inside D
            rem = 180.0 - j * Bm
            if rem < -1e-9:
                continue
            for n in range(max(nmin, M, j), 12):
                k = n - j                                # discs in D \ S
                free = 11 - n - M + j                    # discs in neither set
                if free < 0:
                    continue
                if k == 0:
                    if rem > 1e-9:
                        continue
                    s = Am + free * Ainf
                else:
                    if rem > k * Bmaxd + 1e-9:
                        continue
                    s = Am + k * h(rem / k) + free * Ainf
                if s > best:
                    best, bestinfo = s, dict(j=j, n=n, k=k, free=free,
                                             rem=rem, Bm=Bm, Am=Am)
        rows.append(dict(M=M, Am=Am, bound=best, info=bestinfo,
                         betas=[round(p["beta"], 3) for p in picks[:M]],
                         As=[round(p["A"], 3) for p in picks[:M]],
                         dmaxs=[round(p["dmax"], 3) for p in picks[:M]]))
    bmin = min(rows, key=lambda z: z["bound"])
    return dict(rows=rows, best=bmin, Bmax_deg=Bmaxd, nmin=nmin,
                Ainf=float(np.degrees(Ainf)))


def main():
    r = float(sys.argv[1]) if len(sys.argv) > 1 else U
    print("r = %.18f" % r)
    res = {}
    for e in [0.0, 0.005, 0.01, 0.02, 0.03, 0.04, 0.045, 0.05, 0.055, 0.06,
              0.065, 0.07, 0.075, 0.08, 3.0 * r - 1.0]:
        c = combined(r, e)
        Bmax, h2max = concavity_check(r, e)
        tag = "EXCLUDES k=11" if c and c["best"]["bound"] < 180.0 else "----"
        print("  e=%.5f  h_concavity(max h'')=%+.3e  Bmax=%6.3f nmin=%2d  "
              "M*=%2d  bound=%9.3f deg   %s"
              % (e, h2max, np.degrees(Bmax), c["nmin"],
                 c["best"]["M"], c["best"]["bound"], tag), flush=True)
        res["%.5f" % e] = dict(best=c["best"], Bmax_deg=c["Bmax_deg"],
                               nmin=c["nmin"], Ainf=c["Ainf"],
                               h2max=h2max)
    json.dump(res, open("comb_lb_out.json", "w"), indent=1)


if __name__ == "__main__":
    main()
