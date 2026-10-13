"""certify_ring2.py -- directed-endpoint interval certificate of the k=10 dual
over the ring continuous domain at a FIXED hub configuration.

The certified statement, the rigour design and the caveats are described in
DUAL.md section 5b.  Summary: at the exact rational configuration
t1 = t2 = 1/5, delta = 604457/200000 (d > 0 asserted, merge branch NOT used) and
the exact rational dual weights (schema [w0, cos1..cosK, sin1..sinK], K = 4) we
certify   cap(rho,phi) < req_lo/10   for all (rho,phi) in the ring domain.

Rigour: every load-bearing quantity is an mpmath.iv interval; endpoints are
extracted as exact mpf values only to rebuild intervals (self-checked); the
undecided arc-intersection case uses the directed bound [lo.a, hi.b] (the true
endpoints lie inside it) with no padding; the direction of (c - h_j) is enclosed
by the hull of the four rigorously enclosed vertex angles (valid because the
polar rectangle minus h_j is compact and does not contain the origin, and the
polar angle is monotone along every segment whose line avoids the origin).
"""
from __future__ import annotations

import json
import sys
import time
from fractions import Fraction
from pathlib import Path

from mpmath import iv, mp

HERE = Path(__file__).resolve().parent
OUT = HERE.parent / "evidence"

U_FR = Fraction(22568935234031792038557518369, 62500000000000000000000000000)
DELTA = Fraction(604457, 200000)
T1 = Fraction(1, 5)
T2 = Fraction(1, 5)
K = 4
PER = 1 + 2 * K


def load_weights(path=None):
    p = path or (OUT / "rational_dual_worst.json")
    d = json.load(open(p))
    raw = ([b["rational"] for b in d["blocks"]] if "blocks" in d else d["weights"])
    return [[Fraction(s) for s in blk] for blk in raw], d


def ivf(fr: Fraction):
    return iv.mpf(fr.numerator) / iv.mpf(fr.denominator)


def elo(x):
    return mp.mpf(x.a)


def ehi(x):
    return mp.mpf(x.b)


def clip_unit(x, tag=""):
    """intersect with [-1,1] (valid when the true value lies in [-1,1])."""
    a, b = elo(x), ehi(x)
    if a < -1:
        a = mp.mpf(-1)
    if b > 1:
        b = mp.mpf(1)
    return iv.mpf([a, b])


class Cert:
    def __init__(self, W, dps=25):
        iv.dps = dps
        mp.dps = dps + 15
        self.check_extraction()
        self.W = [[ivf(c) for c in blk] for blk in W]
        self.U = ivf(U_FR)
        self.h1 = [ivf(T1), iv.mpf(0)]
        self.h2 = [ivf(T2) * iv.cos(ivf(DELTA)), ivf(T2) * iv.sin(ivf(DELTA))]
        dx = self.h1[0] - self.h2[0]
        dy = self.h1[1] - self.h2[1]
        self.d = iv.sqrt(dx * dx + dy * dy)
        assert (self.d > 1e-6) is True, "merge branch not implemented: need d>0"
        q = clip_unit(self.d / (2 * self.U))
        self.b = iv.atan2(iv.sqrt(1 - q ** 2), q)
        self.away = [iv.atan2(dy, dx), iv.atan2(-dy, -dx)]
        self.E = [(self.away[0], iv.pi - self.b), (self.away[1], iv.pi - self.b)]
        self.req = self._req()
        self.rho_lo = iv.mpf(1) - self.U
        self.rho_hi = iv.sqrt(1 - self.U * self.U)
        self.two_pi = 2 * iv.pi

    @staticmethod
    def check_extraction():
        for (p, q) in ((1, 7), (2, 3), (-5, 11)):
            x = ivf(Fraction(p, q)) * iv.pi
            y = iv.mpf([elo(x), ehi(x)])
            assert (y.a <= x.a) is True and (x.b <= y.b) is True, "extraction"

    def F(self, coef, th):
        s = coef[0] * th
        for k in range(1, K + 1):
            s += coef[k] * iv.sin(k * th) / k
            s -= coef[K + k] * iv.cos(k * th) / k
        return s

    def arc(self, coef, c_iv, h_iv):
        return self.F(coef, c_iv + h_iv) - self.F(coef, c_iv - h_iv)

    def _req(self):
        tot = self.arc(self.W[0], iv.mpf(0), iv.pi)
        for j in (0, 1):
            c, h = self.E[j]
            tot += self.arc(self.W[j + 1], c, h)
        return tot

    def box_upper(self, r0, r1, p0, p1):
        rho = iv.mpf([r0, r1])
        phi = iv.mpf([p0, p1])
        arg = clip_unit((1 + rho * rho - self.U * self.U) / (2 * rho))
        al = iv.atan2(iv.sqrt(1 - arg ** 2), arg)
        ub = self.arc(self.W[0], phi, al)
        for j, hj in enumerate((self.h1, self.h2)):
            # --- EXPLICIT monotonicity guard (Lead 2026-09-26):
            # along the curved edge rho=const the derivative of
            # arg(rho u_phi - h) in phi equals rho*(rho - <h,u_phi>)/ell^2,
            # which is strictly positive as soon as rho_min > |h|_max.
            # On the radial edges (phi=const) the argument is constant.
            # Hence the argument extremes over the polar box are attained at
            # its four CORNERS.  Without this guard the statement would be
            # false (and no rectangle/straight-edge argument is used).
            hmax = iv.sqrt(hj[0] * hj[0] + hj[1] * hj[1])
            if not ((mp.mpf(r0) > ehi(hmax)) is True):
                return None, False          # guard violated -> split the box
            # --- branch-continuation guard (Lead 2026-09-26): a common vertex
            # span < pi is NOT enough by itself (if the phi-box were as wide as
            # 2*pi the four corners could coincide).  We bound the total angular
            # variation of psi over the box by explicit derivatives and require
            # it to stay below pi (so no 2*pi wrap can occur, and the vertex
            # lifts are comparable).  Derivative bounds on the polar box:
            #   |d psi/d phi| = rho(rho - <h,u_phi>)/ell^2
            #                 <= rho_max (rho_max + |h|) / (rho_min - |h|)^2
            #   |d psi/d rho| = |cross(h,u_phi)|/ell^2
            #                 <= |h| / (rho_min - |h|)^2
            #   |d psi/d h|   <= 1/(rho_min - |h|)
            rmin = mp.mpf(r0)
            rmx = mp.mpf(r1)
            hmx = ehi(hmax)
            den = rmin - hmx
            if den <= 0:
                return None, False
            g1 = ehi((iv.mpf([r1, r1]) * (iv.mpf([r1, r1]) + hmax)) / (den ** 2))
            g2 = ehi(hmax / (den ** 2))
            g3 = ehi(iv.mpf([1, 1]) / den)
            dh = (ehi(hj[0]) - elo(hj[0])) + (ehi(hj[1]) - elo(hj[1]))
            V = g1 * (mp.mpf(p1) - mp.mpf(p0)) + g2 * (rmx - rmin) + g3 * dh
            if not (V < elo(iv.pi)):
                return None, False          # variation may reach pi -> split
            # --- rigorous (conservative) test: may the polar rectangle contain
            #     h_j?  If it may, the direction psi_j is undefined and the box
            #     is split instead of bounded.
            n2 = hj[0] * hj[0] + hj[1] * hj[1]
            r_lo2 = mp.mpf(r0) ** 2
            r_hi2 = mp.mpf(r1) ** 2
            radial_maybe = not ((ehi(n2) < r_lo2) is True or (elo(n2) > r_hi2) is True)
            if radial_maybe:
                a_hj = iv.atan2(hj[1], hj[0])
                ang_maybe = False
                for shift in (-2 * mp.pi, 0, 2 * mp.pi):
                    lo_, hi_ = mp.mpf(p0) + shift, mp.mpf(p1) + shift
                    if not ((ehi(a_hj) < lo_) is True or (elo(a_hj) > hi_) is True):
                        ang_maybe = True
                        break
                if ang_maybe:
                    return None, False
            Xs, Ys, ok = [], [], False
            for rr in (r0, r1):
                for pp in (p0, p1):
                    cc = iv.cos(iv.mpf([pp, pp]))
                    ss = iv.sin(iv.mpf([pp, pp]))
                    X = iv.mpf([rr, rr]) * cc - hj[0]
                    Y = iv.mpf([rr, rr]) * ss - hj[1]
                    Xs.append(X)
                    Ys.append(Y)
                    if (X.a > 0) is True or (X.b < 0) is True or \
                       (Y.a > 0) is True or (Y.b < 0) is True:
                        ok = True
            if not ok:
                return None, False
            angs = [iv.atan2(Y, X) for X, Y in zip(Xs, Ys)]
            # --- lift by integer multiples of 2*pi.  The integer k_i is chosen
            # by a float heuristic (allowed), but its consistency is *verified*:
            # the lifted corner intervals must fit in a window of width
            # < pi - V, where V is an explicit upper bound of the total angular
            # variation of psi over the box (curved edges: d/dphi = rho(rho -
            # <h,u>)/ell^2 <= rho_max(rho_max+|h|)/lmin^2; radial edges:
            # |d/drho| = |<u x h>|/ell^2 <= |h|/lmin^2, sign independent of rho;
            # hub direction: <= 1/lmin), lmin = rho_min - |h|_max > 0.
            lmin_lo = elo(iv.mpf([r0, r0]) - hmax)
            if not (lmin_lo > 0):
                return None, False
            inv2 = ehi(iv.mpf([1, 1]) / (iv.mpf([lmin_lo, lmin_lo]) ** 2))
            dphi = ehi(iv.mpf([p1, p1]) - iv.mpf([p0, p0]))
            drho = ehi(iv.mpf([r1, r1]) - iv.mpf([r0, r0]))
            rmx = ehi(iv.mpf([r1, r1]))
            hmxu = ehi(hmax)
            V = ehi(iv.mpf([drho, drho]) * iv.mpf([hmxu, hmxu]) *
                    iv.mpf([inv2, inv2]) +
                    iv.mpf([dphi, dphi]) * iv.mpf([rmx, rmx]) *
                    (iv.mpf([rmx, rmx]) + iv.mpf([hmxu, hmxu])) *
                    iv.mpf([inv2, inv2]))
            base = (elo(angs[0]) + ehi(angs[0])) / 2
            lifted, los, his = [], [], []
            for a in angs:
                m = (elo(a) + ehi(a)) / 2
                k = 0
                while m + 2 * float(mp.pi) * k - base > float(mp.pi):
                    k -= 1
                while m + 2 * float(mp.pi) * k - base < -float(mp.pi):
                    k += 1
                al = a + k * self.two_pi
                lifted.append(al)
                los.append(elo(al))
                his.append(ehi(al))
            span = iv.mpf([max(his), max(his)]) - iv.mpf([min(los), min(los)])
            if not (span + iv.mpf([V, V]) < iv.pi):
                return None, False                 # lift/window undecided -> split
            # Same-lift-branch continuity is now PROVED by span + V < pi, so the
            # four-corner extremum argument applies on a single branch and the
            # direction enclosure needs no extra V inflation (Lead 2026-09-26:
            # adding V to psi is conservative redundancy).
            psi = iv.mpf([min(los), max(his)])
            cx = rho * iv.cos(phi)
            cy = rho * iv.sin(phi)
            dx = cx - hj[0]
            dy = cy - hj[1]
            ell = iv.sqrt(dx * dx + dy * dy)
            if (ell > 2 * self.U) is True:
                continue
            if (ell < 2 * self.U) is True:
                q = clip_unit(ell / (2 * self.U))
            else:
                q = clip_unit(iv.mpf([elo(ell), elo(ell)]) / (2 * self.U))
            bet = iv.atan2(iv.sqrt(1 - q ** 2), q)
            cE, hE = self.E[j]
            for sh in (-1, 0, 1):
                s2 = sh * self.two_pi            # interval multiple of 2*pi
                aa = psi - bet + s2
                bb = psi + bet + s2
                EL = cE - hE                    # E_j = [cE-hE, cE+hE]
                ER = cE + hE
                lo = iv.mpf([max(elo(EL), elo(aa)), max(ehi(EL), ehi(aa))])
                hi = iv.mpf([min(elo(ER), elo(bb)), min(ehi(ER), ehi(bb))])
                if (lo < hi) is True:
                    ub += self.arc(self.W[j + 1], (lo + hi) / 2, (hi - lo) / 2)
                elif (hi < lo) is True:
                    continue
                else:
                    # directed undecided bound, computed entirely in the iv
                    # context (no mp subtraction): the true intersection lies in
                    # [lo_lower, hi_upper] and W >= 0, so
                    #   int <= F(hi_upper) - F(lo_lower)
                    fhi = self.F(self.W[j + 1],
                                 iv.mpf([ehi(hi), ehi(hi)]))
                    flo = self.F(self.W[j + 1],
                                 iv.mpf([elo(lo), elo(lo)]))
                    ub += fhi - flo                # interval difference, upper end used
        return ub, True

    def run(self, thr_scale=1.0, max_boxes=60000, nrho0=10, nphi0=40,
            max_depth=18, accept_frac=0.9995, verbose=True):
        # threshold: rigorous lower bound of req_lo/10 built entirely inside iv
        # (no mpf rounding nudge), optionally scaled by an exact rational.
        scale_iv = ivf(Fraction(str(thr_scale)).limit_denominator(10 ** 9))
        th_iv = (self.req / 10) * scale_iv
        th = elo(th_iv)
        th_accept = th * accept_frac
        # grid endpoints: taken from interval enclosures outward, so the union of
        # boxes provably covers the whole ring domain (no padding, no float
        # rounding argument needed: c0 <= 1-U and cN >= sqrt(1-U^2) hold by
        # construction with exact mpf endpoints of the enclosures).
        rl = elo(self.rho_lo)
        rh = ehi(self.rho_hi)
        plo = mp.mpf(0)
        phi_hi = ehi(self.two_pi)
        stack = []
        for i in range(nrho0):
            for j in range(nphi0):
                stack.append((rl + (rh - rl) * i / nrho0, rl + (rh - rl) * (i + 1) / nrho0,
                              plo + (phi_hi - plo) * j / nphi0,
                              plo + (phi_hi - plo) * (j + 1) / nphi0, 0))
        nbox = leaves = 0
        worst_leaf = (-1, None)
        worst_any = (-1, None)
        maxdepth = 0
        fails = []
        t0 = time.time()
        while stack:
            (r0, r1, p0, p1, d) = stack.pop()
            nbox += 1
            maxdepth = max(maxdepth, d)
            if nbox > max_boxes:
                fails.append(dict(rho=[str(r0), str(r1)], phi=[str(p0), str(p1)],
                                  depth=d, why="box_limit"))
                continue
            ub, ok = self.box_upper(r0, r1, p0, p1)
            if not ok:
                if d >= max_depth:
                    fails.append(dict(rho=[str(r0), str(r1)], phi=[str(p0), str(p1)],
                                      depth=d, why="undecided-direction"))
                    continue
                rm, pm = (r0 + r1) / 2, (p0 + p1) / 2
                for (a0, a1) in ((r0, rm), (rm, r1)):
                    for (b0, b1) in ((p0, pm), (pm, p1)):
                        stack.append((a0, a1, b0, b1, d + 1))
                continue
            ubv = ehi(ub)
            if ubv > worst_any[0]:
                worst_any = (ubv, (r0, r1, p0, p1))
            if (ub < th_accept) is True:
                leaves += 1
                if ubv > worst_leaf[0]:
                    worst_leaf = (ubv, (r0, r1, p0, p1))
                continue
            if d >= max_depth:
                fails.append(dict(rho=[str(r0), str(r1)], phi=[str(p0), str(p1)],
                                  depth=d, ub=str(ubv), why="over_threshold"))
                continue
            rm, pm = (r0 + r1) / 2, (p0 + p1) / 2
            for (a0, a1) in ((r0, rm), (rm, r1)):
                for (b0, b1) in ((p0, pm), (pm, p1)):
                    stack.append((a0, a1, b0, b1, d + 1))
            if verbose and nbox % 100000 == 0:
                print("   ... %d boxes, %d leaves, %d unsolved, %.0fs"
                      % (nbox, leaves, len(fails), time.time() - t0), flush=True)
        return dict(nbox=nbox, leaves=leaves, unsolved=len(fails), maxdepth=maxdepth,
                    worst_leaf_ub=str(worst_leaf[0]),
                    worst_leaf_box=[str(x) for x in worst_leaf[1]] if worst_leaf[1] else None,
                    worst_any_ub=str(worst_any[0]),
                    req_lo=str(self.req.a), req_hi=str(self.req.b),
                    threshold=str(th), margin_ratio=str(worst_leaf[0] / th),
                    thr_scale=thr_scale, secs=time.time() - t0,
                    fail_examples=fails[:6])


def main():
    max_boxes = int(sys.argv[1]) if len(sys.argv) > 1 else 60000
    dps = int(sys.argv[2]) if len(sys.argv) > 2 else 25
    thr_scale = float(sys.argv[3]) if len(sys.argv) > 3 else 1.0
    max_depth = int(sys.argv[4]) if len(sys.argv) > 4 else 14
    W, meta = load_weights()
    c = Cert(W, dps=dps)
    print("directed-endpoint kernel; t1=t2=1/5, delta=604457/200000, d>0 asserted")
    print("req in [%s, %s]" % (c.req.a, c.req.b))
    res = c.run(thr_scale=thr_scale, max_boxes=max_boxes, max_depth=max_depth)
    print("threshold = %s   (scale %.4f)" % (res["threshold"], thr_scale))
    print(json.dumps({k: res[k] for k in ("nbox", "leaves", "unsolved", "maxdepth",
                                          "worst_leaf_ub", "margin_ratio", "secs")},
                     indent=1))
    json.dump(res, open(OUT / "certify_ring2.json", "w"), indent=1)


if __name__ == "__main__":
    main()
