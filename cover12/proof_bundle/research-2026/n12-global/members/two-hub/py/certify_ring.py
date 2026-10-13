"""certify_ring.py -- interval certificate over the ring continuous domain for a
FIXED hub configuration and FIXED rational dual (mpmath interval arithmetic).

Statement certified (exact rational hub config t1=t2=1/5, delta=604457/200000,
exact rational weights of evidence/rational_dual_worst.json, U the exact rational
22568935234031792038557518369/62500000000000000000000000000):

    for all (rho,phi) in [1-U, sqrt(1-U^2)] x [0,2pi):
        cap(rho,phi) := int_{A0}W0 + int_{E1 cap A1}W1 + int_{E2 cap A2}W2
        <  req_lo/10 ,     req_lo = rigorous lower bound of
                                   int_{S^1}W0 + int_{E1}W1 + int_{E2}W2.

Design (all interval operations are inclusion-monotone; no endpoint is ever
extracted by value, so rounding cannot break rigour):
 * arc integral via the antiderivative F; bound for a box = sup F([hi]) - inf F([lo]).
 * the ring-side angle psi_j = atan2(c-h_j) is enclosed as the hull of the four
   vertex directions (valid: a rectangle not containing the origin has its angle
   range attained at vertices, since the angle is strictly monotone on each edge
   whose supporting line avoids the origin); if the rectangle contains h_j the
   box is split instead.
 * the intersection A_j cap E_j is treated shift by shift (-2pi,0,+2pi):
   definite emptiness is skipped, definite non-emptiness is included, and any
   undecided case triggers a bisection (rigorous interval comparisons only:
   `x<y` is True exactly when sup x < inf y).
 * clipping of acos arguments to [-1,1] is used only where the true argument is
   known to lie in that range.
"""
from __future__ import annotations

import json
import math
import sys
import time
from fractions import Fraction
from pathlib import Path

from mpmath import iv, mp

HERE = Path(__file__).resolve().parent
OUT = HERE.parent / "evidence"

U_FR = Fraction(22568935234031792038557518369, 62500000000000000000000000000)
DELTA = Fraction(604457, 200000)      # 3.022285
K = 4


def load_weights(path=None):
    p = path or (OUT / "rational_dual_worst.json")
    d = json.load(open(p))
    return [[Fraction(s) for s in blk] for blk in d["weights"]], d


def ivf(fr: Fraction):
    return iv.mpf(fr.numerator) / iv.mpf(fr.denominator)


def clip_unit(x):
    """intersect the interval x with [-1,1] (valid only when the true value is
    known to lie inside)."""
    lo = x.b if (x.b < -1) is True else (x.a if (x.a < -1) is True else None)
    hi = x.a if (x.a > 1) is True else (x.b if (x.b > 1) is True else None)
    if lo is None and hi is None:
        return x
    a = -1 if (x.a < -1) is True else x.a
    b = 1 if (x.b > 1) is True else x.b
    return iv.mpf([a, b])


def acos_iv(x):
    return iv.atan2(iv.sqrt(1 - clip_unit(x) ** 2), clip_unit(x))


def Fval(coef, th):
    s = coef[0] * th
    for k in range(1, K + 1):
        s += coef[k] * iv.sin(k * th) / k
        s -= coef[K + k] * iv.cos(k * th) / k
    return s


def arc_upper(coef, c_iv, h_iv):
    return Fval(coef, c_iv + h_iv) - Fval(coef, c_iv - h_iv)


class Certifier:
    def __init__(self, W, dps=25):
        iv.dps = dps
        self.Wfrac = W
        self.W = [[ivf(c) for c in blk] for blk in W]
        self.U = ivf(U_FR)
        self.h1 = [ivf(Fraction(1, 5)), iv.mpf(0)]
        s = ivf(Fraction(1, 5))
        self.h2 = [s * iv.cos(ivf(DELTA)), s * iv.sin(ivf(DELTA))]
        dx = self.h1[0] - self.h2[0]
        dy = self.h1[1] - self.h2[1]
        self.d = iv.sqrt(dx * dx + dy * dy)
        self.b = acos_iv(self.d / (2 * self.U))
        self.away1 = iv.atan2(dy, dx)
        self.away2 = iv.atan2(-dy, -dx)
        self.E = [(self.away1, iv.pi - self.b), (self.away2, iv.pi - self.b)]
        self.req_lo = self._req_lower()
        self.rho_lo = 1 - self.U
        self.rho_hi = iv.sqrt(1 - self.U * self.U)
        self.threshold = self.req_lo / 10
        self.two_pi = 2 * iv.pi

    def _req_lower(self):
        tot = arc_upper(self.W[0], iv.mpf(0), iv.pi)
        for j in (0, 1):
            c, h = self.E[j]
            tot += arc_upper(self.W[j + 1], c, h)
        return tot  # interval; the caller uses its lower end

    def box_upper(self, r0, r1, p0, p1):
        """Return (upper bound as iv, ok).  ok=False means: split this box."""
        rho = iv.mpf([r0, r1])
        phi = iv.mpf([p0, p1])
        al = acos_iv((1 + rho * rho - self.U * self.U) / (2 * rho))
        ub = arc_upper(self.W[0], phi, al)
        cx = rho * iv.cos(phi)
        cy = rho * iv.sin(phi)
        corners = [(r0 * math.cos(p0), r0 * math.sin(p0)),
                   (r0 * math.cos(p1), r0 * math.sin(p1)),
                   (r1 * math.cos(p0), r1 * math.sin(p0)),
                   (r1 * math.cos(p1), r1 * math.sin(p1))]
        for j, hj in enumerate((self.h1, self.h2)):
            hxa = iv.mpf([corners[0][0], corners[0][0]])
            # exact containment test of the hub in the (rho,phi) rectangle
            hxv = float(mp.mpf(hj[0].a))
            hyv = float(mp.mpf(hj[1].a))
            if min(c[0] for c in corners) <= hxv <= max(c[0] for c in corners) and \
               min(c[1] for c in corners) <= hyv <= max(c[1] for c in corners):
                return None, False
            # direction of (c - h_j): reference-relative enclosure.
            # reference vector = box-centre point minus h_j (frozen floats,
            # used only to keep the relative angles small; the enclosure itself
            # is built from the rigorous interval sum below).
            rc = 0.5 * (r0 + r1)
            pc = 0.5 * (p0 + p1)
            xref = iv.mpf([rc * math.cos(pc), rc * math.cos(pc)]) - hj[0]
            yref = iv.mpf([rc * math.sin(pc), rc * math.sin(pc)]) - hj[1]
            psi_ref = iv.atan2(yref, xref)
            rels = []
            ok_angles = True
            for (xv, yv) in corners:
                xv_iv = iv.mpf([xv, xv]) - hj[0]
                yv_iv = iv.mpf([yv, yv]) - hj[1]
                cross = xv_iv * yref - yv_iv * xref
                dot = xv_iv * xref + yv_iv * yref
                r = iv.atan2(cross, dot)
                rels.append(r)
                if (r.a > -math.pi / 2) is not True or (r.b < math.pi / 2) is not True:
                    ok_angles = False
            if not ok_angles:
                return None, False
            rel_lo = min(float(mp.mpf(r.a)) for r in rels) - 1e-9
            rel_hi = max(float(mp.mpf(r.b)) for r in rels) + 1e-9
            psi = psi_ref + iv.mpf([rel_lo, rel_hi])
            dx = cx - hj[0]
            dy = cy - hj[1]
            ell = iv.sqrt(dx * dx + dy * dy)
            if (ell > 2 * self.U) is True:
                continue                          # no arc, rigorous
            if (ell < 2 * self.U) is True:
                bet = acos_iv(ell / (2 * self.U))
            else:
                # arc appears/disappears inside this box: use the largest
                # possible halfwidth (valid over-estimate, no undecided case)
                bet = acos_iv(iv.mpf([ell.a, ell.a]) / (2 * self.U))
            cE, hE = self.E[j]
            for sh in (-1, 0, 1):
                shift = sh * self.two_pi
                lo = iv.mpf([max(cE.a, (psi - bet + shift).a),
                             max(cE.b, (psi - bet + shift).b)])
                hi = iv.mpf([min(cE.a, (psi + bet + shift).a),
                             min(cE.b, (psi + bet + shift).b)])
                if (lo < hi) is True:
                    ub += arc_upper(self.W[j + 1], (lo + hi) / 2, (hi - lo) / 2)
                elif (hi < lo) is True:
                    continue
                else:
                    # undecided order: over-estimate by the hull bound
                    # (float endpoint extraction padded by 1e-9, which dominates
                    # the ~1e-15 extraction error; a directed-rounding kernel
                    # should replace this step)
                    hl = min(float(mp.mpf(lo.a)), float(mp.mpf(hi.a))) - 1e-9
                    hh = max(float(mp.mpf(lo.b)), float(mp.mpf(hi.b))) + 1e-9
                    ub += arc_upper(self.W[j + 1], (hl + hh) / 2, (hh - hl) / 2)
        return ub, True

    def run(self, max_boxes=60000, nrho0=10, nphi0=40, max_depth=13, verbose=True,
            accept_frac=0.9995):
        th = self.threshold
        th_accept = th * accept_frac
        rl, rh = float(mp.mpf(self.rho_lo.a)), float(mp.mpf(self.rho_hi.b))
        stack = []
        for i in range(nrho0):
            for j in range(nphi0):
                stack.append((rl + (rh - rl) * i / nrho0, rl + (rh - rl) * (i + 1) / nrho0,
                              2 * math.pi * j / nphi0, 2 * math.pi * (j + 1) / nphi0, 0))
        nbox = 0
        t0 = time.time()
        worst_all = (-1e9, None)
        worst_leaf = (-1e9, None)
        leaves = 0
        maxdepth = 0
        fails = []
        while stack:
            (r0, r1, p0, p1, d) = stack.pop()
            nbox += 1
            maxdepth = max(maxdepth, d)
            if nbox > max_boxes:
                fails.append(dict(rho=[r0, r1], phi=[p0, p1], depth=d, why="box_limit"))
                continue
            ub, ok = self.box_upper(r0, r1, p0, p1)
            if not ok:
                if d >= max_depth:
                    fails.append(dict(rho=[r0, r1], phi=[p0, p1], depth=d,
                                      why="undecided"))
                    continue
                rm, pm = (r0 + r1) / 2, (p0 + p1) / 2
                for (a0, a1) in ((r0, rm), (rm, r1)):
                    for (b0, b1) in ((p0, pm), (pm, p1)):
                        stack.append((a0, a1, b0, b1, d + 1))
                continue
            ubv = float(mp.mpf(ub.b))
            if ubv > worst_all[0]:
                worst_all = (ubv, (r0, r1, p0, p1))
            if (ub < th_accept) is True:
                leaves += 1
                if ubv > worst_leaf[0]:
                    worst_leaf = (ubv, (r0, r1, p0, p1))
                continue
            if d >= max_depth:
                fails.append(dict(rho=[r0, r1], phi=[p0, p1], depth=d, ub=ubv,
                                  why="over_threshold"))
                continue
            rm, pm = (r0 + r1) / 2, (p0 + p1) / 2
            for (a0, a1) in ((r0, rm), (rm, r1)):
                for (b0, b1) in ((p0, pm), (pm, p1)):
                    stack.append((a0, a1, b0, b1, d + 1))
            if verbose and nbox % 50000 == 0:
                print("   ... %d boxes, %d leaves, %d unsolved, %.0fs"
                      % (nbox, leaves, len(fails), time.time() - t0), flush=True)
        return dict(nbox=nbox, leaves=leaves, unsolved=len(fails),
                    maxdepth=maxdepth,
                    worst_leaf_ub=worst_leaf[0],
                    worst_leaf_box=list(worst_leaf[1]) if worst_leaf[1] else None,
                    worst_any_ub=worst_all[0],
                    req_lo=float(mp.mpf(self.req_lo.a)), threshold=float(mp.mpf(th.a)),
                    margin_ratio=(worst_leaf[0] / float(mp.mpf(th.a)))
                    if worst_leaf[1] else None,
                    secs=time.time() - t0, fail_examples=fails[:8])


def main():
    max_boxes = int(sys.argv[1]) if len(sys.argv) > 1 else 60000
    dps = int(sys.argv[2]) if len(sys.argv) > 2 else 25
    thr_scale = float(sys.argv[3]) if len(sys.argv) > 3 else 1.0
    max_depth = int(sys.argv[4]) if len(sys.argv) > 4 else 13
    W, meta = load_weights()
    c = Certifier(W, dps=dps)
    c.threshold = c.threshold * thr_scale
    print("threshold scale = %.4f ; max_depth = %d" % (thr_scale, max_depth))
    print("fixed hub config t1=t2=1/5, delta=604457/200000 (cf. float ratio 0.9695)")
    print("req in  [%s, %s]" % (mp.mpf(c.req_lo.a), mp.mpf(c.req_lo.b)))
    print("threshold req_lo/10 = %s" % mp.mpf(c.threshold.a))
    res = c.run(max_boxes=max_boxes, max_depth=max_depth, verbose=True)
    print(json.dumps({k: (str(v) for v in []) and v for k, v in res.items()},
                     indent=1, default=str))
    json.dump(res, open(OUT / "certify_ring.json", "w"), indent=1, default=str)


if __name__ == "__main__":
    main()
