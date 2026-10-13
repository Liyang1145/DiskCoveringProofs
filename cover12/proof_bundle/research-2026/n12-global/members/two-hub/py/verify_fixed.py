"""verify_fixed.py -- corrected-kernel scan + continuous local max + rational dual.

Assembly used (Lead's scheme): any cover at r<=U, enlarged to U, has active
count k' in {10,11} (active disks stay active; the origin-covering disk has
norm <= U so it is inactive at U).  Hence excluding "exact k'=10 at radius U"
together with the k'=11 theorem (other member) excludes k=10 for every r<=U.
At radius U, inactive <=> norm < 1-U strictly, so the two hubs of a k'=10 cover
satisfy |h_j| + U < 1: their disks lie in int D and no D-clip is needed.
Inner-root reduction at radius U is legal; the ring domain is
rho in [1-U, sqrt(1-U^2)] with alpha(rho) the actual arc.

This script: (1) scans the hub domain, (2) refines the worst configurations by
continuous local maximisation of the coupled contribution, (3) emits one
rational dual for the worst configuration, (4) calibrates the trig-basis
integrals against independent quadrature.
"""
from __future__ import annotations

import json
import math
import sys
import time
from fractions import Fraction
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import dual2 as D2  # noqa: E402

U = D2.U
OUT = HERE.parent / "evidence"


def beta(t, a):
    if t <= 0:
        return math.pi
    if t + a <= U:
        return math.pi
    if abs(t - a) >= U:
        return 0.0
    return math.acos(max(-1.0, min(1.0, (t * t + a * a - U * U) / (2 * t * a))))


def domain(ts, a):
    out = []
    for t1 in ts:
        for t2 in ts:
            if t2 < t1 - 1e-15:
                continue
            b1, b2 = beta(t1, a), beta(t2, a)
            dmin = max(0.0, TWO_PI_ - b1 - b2)
            cands = {round(dmin, 6), round(math.pi, 6)}
            if dmin < math.pi:
                cands.add(round((dmin + math.pi) / 2, 6))
            for dl in sorted(cands):
                if dl > math.pi + 1e-12:
                    continue
                if (t1 + a <= U) or (t2 + a <= U) or (b1 + b2 >= 2 * math.pi - dl - 1e-12):
                    out.append((t1, t2, dl, b1, b2))
    return out


TWO_PI_ = 2 * math.pi


def main():
    K = 4
    tmax = 1.0 - U - 1e-6
    a = 1 - 2 * U
    ts = []
    x = 0.0
    while x < tmax:
        ts.append(round(x, 6))
        x += 0.05
    ts.append(tmax)
    cfgs = domain(ts, a)
    print("hub-domain grid: %d configurations (t<1-U, core covered)" % len(cfgs))
    rows = []
    t0 = time.time()
    for (t1, t2, dl, b1, b2) in cfgs:
        r = D2.solve(t1, t2, dl, K=K, sincos=True, n_rho=40, n_phi=144,
                     clip_req=False)
        if not r.get("ok"):
            rows.append(dict(t1=t1, t2=t2, delta=dl, ok=False))
            continue
        rows.append(dict(t1=t1, t2=t2, delta=dl, ok=True, m_star=r["m_star"],
                         beta1=b1, beta2=b2, d=r["geo"]["d"], b=r["geo"]["b"]))
    ms = [r["m_star"] for r in rows if r.get("ok")]
    print("scan done (%.1fs): %d cfg, fails=%d  m* in [%.5f, %.5f]"
          % (time.time() - t0, len(ms), len([r for r in rows if not r.get("ok")]),
             min(ms), max(ms)))
    worst = sorted([r for r in rows if r.get("ok")], key=lambda r: -r["m_star"])[:6]
    for r in worst:
        print("   worst t1=%.4f t2=%.4f delta=%.4f  m*(grid)=%.5f"
              % (r["t1"], r["t2"], r["delta"], r["m_star"]))
    json.dump(rows, open(OUT / "dual_scan_fixedK.json", "w"), indent=1)

    # ---------------- continuous local refinement at the worst configurations
    print("\ncontinuous local maximisation of the coupled contribution:")
    refined = []
    for r in worst[:3]:
        sol = D2.solve(r["t1"], r["t2"], r["delta"], K=K, sincos=True,
                       n_rho=40, n_phi=144, clip_req=False)
        val, arg = D2.refine_max(sol, sol["m_basis"], K=K, sincos=True, n_start=16)
        req = float(sol["req"] @ sol["m_basis"])
        refined.append(dict(t1=r["t1"], t2=r["t2"], delta=r["delta"],
                            m_grid=r["m_star"], m_local=val, arg=list(arg),
                            ratio=10 * val / req))
        print("   t1=%.4f t2=%.4f delta=%.4f  m_grid=%.6f m_local=%.6f  "
              "10*m_local/req=%.6f" % (r["t1"], r["t2"], r["delta"], r["m_star"],
                                       val, 10 * val / req))
    json.dump(refined, open(OUT / "dual_refined_fixedK.json", "w"), indent=1)

    # ---------------- rational dual at the worst configuration
    r = worst[0]
    sol = D2.solve(r["t1"], r["t2"], r["delta"], K=K, sincos=True, n_rho=40,
                   n_phi=144, clip_req=False)
    per = sol["per"]
    wf = sol["m_basis"]
    den = 10 ** 5

    def round_dual(v):
        """round to rationals while keeping a_0 >= sum|a_k| (nonnegativity)."""
        out = []
        for j in range(3):
            coef = v[j * per:(j + 1) * per]
            a0 = Fraction(int(math.floor(coef[0] * den)), den)
            rest = []
            for c in coef[1:]:
                f = Fraction(round(c * den), den)
                rest.append(f)
            s = sum(abs(f) for f in rest)
            if a0 < s:
                a0 = Fraction(int(math.ceil(s * den)) + 1, den)
            out.append([a0] + rest)
        return out

    wr = round_dual(wf)
    K_ = K

    def eval_cap(wrats, rho, phi):
        v = 0.0
        ah = math.acos(max(-1, min(1, (1 + rho * rho - U * U) / (2 * rho))))
        blk = D2.basis_arc(phi, ah, True, K_)
        v += float(sum(float(wrats[0][i]) * blk[i] for i in range(len(blk))))
        h1, h2, d, b, E = (sol["geo"][k] for k in ("h1", "h2", "d", "b", "E"))
        c = rho * np.array([math.cos(phi), math.sin(phi)])
        for j, hj in enumerate((h1, h2)):
            ell = float(np.hypot(*(c - hj)))
            if ell < 2 * U:
                bet = math.acos(max(-1.0, min(1.0, ell / (2 * U))))
                psi = math.atan2(*(c - hj)[::-1])
                B2 = D2.basis_arc_int(psi, bet, E[j][0], E[j][1], True, K_)
                v += float(sum(float(wrats[j + 1][i]) * B2[i] for i in range(len(B2))))
        return v

    def eval_req(wrats):
        per = 1 + 2 * K_
        req = 0.0
        b0 = D2.basis_arc(0.0, math.pi, True, K_)
        req += sum(float(wrats[0][i]) * b0[i] for i in range(per))
        for j in range(2):
            cw, hw = sol["geo"]["E"][j]
            bj = D2.basis_arc(cw, hw, True, K_)
            req += sum(float(wrats[j + 1][i]) * bj[i] for i in range(per))
        return req

    # verify rational dual on a fine grid + local refinement
    n_r, n_p = 80, 288
    best = (-1.0, None)
    for rho in np.linspace(1.0 - U, math.sqrt(1.0 - U * U), n_r):
        for phi in np.linspace(0, TWO_PI_, n_p, endpoint=False):
            v = eval_cap(wr, float(rho), float(phi))
            if v > best[0]:
                best = (v, (float(rho), float(phi)))
    print("\nrational dual at t1=%.4f t2=%.4f delta=%.4f:" % (r["t1"], r["t2"], r["delta"]))
    print("   fine grid cp=(%.6f,%.6f): max cap=%.7f  req=%.7f  10*cap/req=%.6f"
          % (best[1][0], best[1][1], best[0], eval_req(wr), 10 * best[0] / eval_req(wr)))
    # local refinement with rational weights
    from scipy.optimize import minimize as _mz
    bb = (-1.0, None)
    for i in range(6):
        x0 = np.array(best[1]) + np.array([0.004 * i, 0.02 * i])
        res = _mz(lambda x: -eval_cap(wr, x[0], x[1]), x0, method="Nelder-Mead",
                  options=dict(xatol=1e-13, fatol=1e-15, maxfev=6000, adaptive=True))
        if -res.fun > bb[0]:
            bb = (-res.fun, res.x.copy())
    print("   local max cap=%.7f at (%.6f,%.6f)   10*cap/req=%.6f  %s"
          % (bb[0], bb[1][0], bb[1][1], 10 * bb[0] / eval_req(wr),
             "PASS" if 10 * bb[0] < eval_req(wr) else "FAIL"))
    out = dict(t1=r["t1"], t2=r["t2"], delta=r["delta"], K=K,
               weights=[[str(c) for c in wrow] for wrow in wr],
               req=eval_req(wr), cap_local=bb[0], arg=list(bb[1]),
               ratio=10 * bb[0] / eval_req(wr))
    json.dump(out, open(OUT / "rational_dual_worst.json", "w"), indent=1)

    # ---------------- independent quadrature calibration
    print("\nquadrature calibration of the coupled contribution (same weights):")
    chk = []
    for (rho, phi) in [(0.64, 0.0), (0.70, 1.0), (0.85, 2.0), (0.93, 3.0),
                       (0.66, 4.5)]:
        ah = math.acos(max(-1, min(1, (1 + rho * rho - U * U) / (2 * rho))))
        v_basis = 0.0
        v_quad = 0.0
        w0 = [float(x) for x in wr[0]]
        v_basis += float(sum(w0[i] * D2.basis_arc(phi, ah, True, K_)[i]
                             for i in range(len(w0))))
        v_quad += D2.quad_int_arc(w0, phi, ah, True, K_, n=20001)
        h1, h2, d, b, E = (sol["geo"][k] for k in ("h1", "h2", "d", "b", "E"))
        c = rho * np.array([math.cos(phi), math.sin(phi)])
        for j, hj in enumerate((h1, h2)):
            ell = float(np.hypot(*(c - hj)))
            if ell < 2 * U:
                bet = math.acos(max(-1.0, min(1.0, ell / (2 * U))))
                psi = math.atan2(*(c - hj)[::-1])
                wj = [float(x) for x in wr[j + 1]]
                B2 = D2.basis_arc_int(psi, bet, E[j][0], E[j][1], True, K_)
                v_basis += float(sum(wj[i] * B2[i] for i in range(len(B2))))
                v_quad += D2.quad_int_arc_int(wj, psi, bet, E[j][0], E[j][1],
                                              True, K_, n=200001)
        chk.append(dict(rho=rho, phi=phi, basis=v_basis, quad=v_quad,
                        diff=v_basis - v_quad))
        print("   rho=%.3f phi=%.2f  basis=%.9f quad=%.9f  diff=%.2e"
              % (rho, phi, v_basis, v_quad, v_basis - v_quad))
    json.dump(chk, open(OUT / "quad_calibration.json", "w"), indent=1)
    # also calibrate the requirement integral (E_j ints) by quadrature
    rq = 0.0
    w0 = [float(x) for x in wr[0]]
    rq += D2.quad_int_arc(w0, 0.0, math.pi, True, K_, n=20001)
    for j in range(2):
        cw, hw = sol["geo"]["E"][j]
        wj = [float(x) for x in wr[j + 1]]
        rq += D2.quad_int_arc(wj, D2.wrap(cw), hw, True, K_, n=200001)
    print("   requirement: basis=%.9f quad=%.9f diff=%.2e"
          % (eval_req(wr), rq, eval_req(wr) - rq))
    json.dump(dict(req_basis=eval_req(wr), req_quad=rq),
              open(OUT / "quad_req.json", "w"), indent=1)


if __name__ == "__main__":
    main()
