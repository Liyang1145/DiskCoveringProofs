"""crosscheck_kernel.py -- REQUIRED verification after the intersection bug:

for 1000 random single ring positions (rho,phi), the interval enclosure of cap
produced by the kernel (degenerate box) MUST contain the independently computed
actual capacity value:

   * reference A: dual2's arc/intersection machinery (float),
   * reference B (for a subset): brute-force quadrature of
     int_{A0}W0 + sum_j int_{E_j cap A_j} W_j , with the E_j cap A_j membership
     tested pointwise on a dense theta grid (completely independent of the
     basis/arc-intersection code paths).

A failure means the interval kernel does not enclose the true value (or the
references disagree beyond tolerance).
"""
from __future__ import annotations

import json
import math
import random
import sys
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import certify_ring2 as C2  # noqa: E402
import dual2 as D2  # noqa: E402

from mpmath import iv, mp

OUT = HERE.parent / "evidence"


def weight_val(coefs, th):
    v = coefs[0]                      # constant term (missing earlier -> negative refB)
    for k in range(1, C2.K + 1):
        v += coefs[k] * math.cos(k * th)
        v += coefs[C2.K + k] * math.sin(k * th)
    return v


def main():
    W, meta = C2.load_weights()
    Wf = [[float(c) for c in blk] for blk in W]
    c = C2.Cert(W, dps=25)
    # hub geometry (floats) for the independent references
    h1, h2, d, b, E = (c.h1, c.h2, c.d, c.b, c.E)
    h1f = [float(mp.mpf(h1[0].a)), float(mp.mpf(h1[1].a))]
    h2f = [float(mp.mpf(h2[0].a)), float(mp.mpf(h2[1].a))]
    away1 = math.atan2(h1f[1] - h2f[1], h1f[0] - h2f[0])
    away2 = math.atan2(h2f[1] - h1f[1], h2f[0] - h1f[0])
    bf = float(mp.mpf(c.b.a))
    E1f = (away1, math.pi - bf)
    E2f = (away2, math.pi - bf)
    U = float(mp.mpf(c.U.a))

    def cap_from_kernel(rho, phi):
        ub, ok = c.box_upper(rho, rho, phi, phi)
        assert ok, "degenerate box rejected"
        return float(mp.mpf(ub.a)), float(mp.mpf(ub.b))

    def cap_ref_A(rho, phi):
        """dual2 machinery: exact arc/intersection basis (float)."""
        per = C2.PER
        v = 0.0
        ah = math.acos(max(-1, min(1, (1 + rho * rho - U * U) / (2 * rho))))
        blk = D2.basis_arc(phi, ah, True, C2.K)
        v += sum(Wf[0][i] * blk[i] for i in range(per))
        cc = rho * np.array([math.cos(phi), math.sin(phi)])
        for j, hj in enumerate((np.array(h1f), np.array(h2f))):
            ell = float(np.hypot(*(cc - hj)))
            if ell < 2 * U:
                bet = math.acos(max(-1.0, min(1.0, ell / (2 * U))))
                psi = math.atan2(*(cc - hj)[::-1])
                cE, hE = (E1f if j == 0 else E2f)
                B2 = D2.basis_arc_int(psi, bet, cE, hE, True, C2.K)
                v += sum(Wf[j + 1][i] * B2[i] for i in range(per))
        return v

    def cap_ref_B(rho, phi, n=400001):
        """brute-force: pointwise membership on the circle."""
        th = np.linspace(-math.pi, math.pi, n, endpoint=False)
        ah = math.acos(max(-1, min(1, (1 + rho * rho - U * U) / (2 * rho))))
        cc = rho * np.array([math.cos(phi), math.sin(phi)])
        tot = 0.0
        m0 = np.abs(np.array([(lambda x: (x + math.pi) % (2 * math.pi) - math.pi)(t - phi) for t in th[::1]])) <= ah
        w0 = np.array([weight_val(Wf[0], t) for t in th])
        tot += float(np.sum(w0[m0]) * (2 * math.pi / n))
        for j, hj in enumerate((np.array(h1f), np.array(h2f))):
            ell = float(np.hypot(*(cc - hj)))
            if ell >= 2 * U:
                continue
            bet = math.acos(max(-1.0, min(1.0, ell / (2 * U))))
            psi = math.atan2(*(cc - hj)[::-1])
            cE, hE = (E1f if j == 0 else E2f)
            da = np.abs(np.array([(lambda x: (x + math.pi) % (2 * math.pi) - math.pi)(t - psi) for t in th]))
            dE = np.abs(np.array([(lambda x: (x + math.pi) % (2 * math.pi) - math.pi)(t - cE) for t in th]))
            m = (da <= bet) & (dE <= hE)
            wj = np.array([weight_val(Wf[j + 1], t) for t in th])
            tot += float(np.sum(wj[m]) * (2 * math.pi / n))
        return tot

    rng = random.Random(20260926)
    fails = []
    rows = []
    for i in range(1000):
        rho = 1 - U + (math.sqrt(1 - U * U) - (1 - U)) * rng.random()
        phi = 2 * math.pi * rng.random()
        lo, hi = cap_from_kernel(rho, phi)
        ra = cap_ref_A(rho, phi)
        if not (lo - 1e-9 <= ra <= hi + 1e-9):
            fails.append(dict(kind="A", rho=rho, phi=phi, lo=lo, hi=hi, ref=ra))
        rows.append((rho, phi, lo, hi, ra))
        if i < 40:
            rb = cap_ref_B(rho, phi, n=200001)
            if not (lo - 2e-5 <= rb <= hi + 2e-5) or abs(rb - ra) > 2e-3:
                fails.append(dict(kind="B", rho=rho, phi=phi, lo=lo, hi=hi,
                                  refA=ra, refB=rb))
    out = dict(n=1000, n_brute=40, fails=len(fails), examples=fails[:5],
               sample=rows[:5])
    json.dump(out, open(OUT / "crosscheck_kernel.json", "w"), indent=1)
    print("cross-check: 1000 points vs dual2 machinery, 40 vs brute force")
    print("failures:", len(fails))
    for f in fails[:5]:
        print("   ", f)


if __name__ == "__main__":
    main()
