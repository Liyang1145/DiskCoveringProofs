"""n12 -- one-hub dual solved in DUAL form, segmented in e (numeric first).

Dual LP (few variables, many rows):
    maximise  pi * sum_r w_r   s.t.   sum_r w_r A[r, p] <= 1  for every
    candidate centre p on a grid,  w >= 0.
A[r,p] are the nonnegative-weight arc functionals (uniform and K=1 Fourier
moments) on S^1 and on |x-h| = U+eps (eps->0; the hub misses that circle).

For a radius-U cover with 11 ring discs and one hub of offset e, summing the
constraint over the 11 centres gives
    pi * sum(w)  <=  11 * sup_p sum_r w_r A[r,p],
so  pi*sum(w) > 11 * (certified sup)  excludes the structure.

The weights depend on e, so the e-range [0, 3U-1] is split into segments; for
each segment the LP is solved at its centre and the largest value over the
segment (grid scan here; rigorous interval version follows) is reported.
"""
import json
import math
import sys
import numpy as np
from scipy.optimize import linprog
from pathlib import Path

U = 0.361102963744508672616920293904
EMAX = 3.0 * U - 1.0
HERE = Path(__file__).parent


def atoms(R, e, nr, nphi, K):
    rho = np.linspace(1.0 - R, 1.0 + R, nr)
    phi = np.arange(nphi) * 2.0 * np.pi / nphi
    rho, phi = np.meshgrid(rho, phi, indexing="ij")
    rho = rho.ravel(); phi = phi.ravel()
    t = np.arccos(np.clip((1.0 + rho * rho - R * R) / (2.0 * rho), -1, 1))
    cx = rho * np.cos(phi); cy = rho * np.sin(phi)
    ell = np.hypot(cx - e, cy); psi = np.arctan2(cy, cx - e)
    beta = np.arccos(np.minimum(1.0, ell / (2.0 * R)))
    rows, names = [], []
    for tag, half, angle in (("boundary", t, phi), ("hub", beta, psi)):
        rows.append(half); names.append(tag + "_uniform")
        for k in range(1, K + 1):
            for kind, phase in (("cos", np.cos(k * angle)),
                                ("sin", np.sin(k * angle))):
                m = np.sin(k * half) / k * phase
                for sign in (-1, 1):
                    rows.append(half + sign * m)
                    names.append(f"{tag}_{kind}{k}_{sign}")
    return np.array(rows), names


def solve_dual(e, K=1, nr=241, nphi=360):
    A, names = atoms(U, e, nr, nphi, K)
    nrows = A.shape[0]
    res = linprog(-np.pi * np.ones(nrows), A_ub=A.T, b_ub=np.ones(A.shape[1]),
                  bounds=(0, None), method="highs")
    assert res.success, res.message
    w = res.x
    return w, names


def sup_on(R, e, w, names, K, nrf=801, nphif=1440):
    Af, nf = atoms(R, e, nrf, nphif, K)
    vals = w @ Af
    j = int(np.argmax(vals))
    idx = np.arange(nrf * nphif)
    rho_j = (1.0 - R) + (2.0 * R) * (idx[j] // nphif) / (nrf - 1.0)
    phi_j = 2.0 * np.pi * (idx[j] % nphif) / nphif
    return float(vals[j]), (float(rho_j), float(phi_j))


def segment(e0, w, names, K, halfwidth, nscan=7):
    es = np.linspace(max(0.0, e0 - halfwidth), min(EMAX, e0 + halfwidth), nscan)
    best = (-1e9, None, None)
    for e in es:
        s, nm = sup_on(U, e, w, names, K)
        if s > best[0]:
            best = (s, float(e), nm)
    return best


def main():
    K = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    nseg = int(sys.argv[2]) if len(sys.argv) > 2 else 12
    edges = np.linspace(0.0, EMAX, nseg + 1)
    out = dict(U=U, EMAX=EMAX, K=K, segments=[])
    print("K=%d  %d segments over e in [0,%.6f]" % (K, nseg, EMAX))
    for i in range(nseg):
        lo, hi = float(edges[i]), float(edges[i + 1])
        e0 = 0.5 * (lo + hi)
        w, names = solve_dual(e0, K)
        sumw = float(np.sum(w))
        target = math.pi * sumw / 11.0
        sup, sup_e, sup_nm = segment(e0, w, names, K, 0.5 * (hi - lo))
        ok = sup < target
        print("  seg %2d e in [%.5f,%.5f] e0=%.5f  sum_w=%.5f  target=%.6f  "
              "sup=%.6f (e=%.5f)  margin=%+.6f  %s"
              % (i, lo, hi, e0, sumw, target, sup, sup_e, target - sup,
                 "ok" if ok else "FAIL"), flush=True)
        out["segments"].append(dict(
            e_lo=lo, e_hi=hi, e0=e0, sum_w=sumw, target=target, sup=sup,
            sup_e=sup_e, margin=target - sup, ok=bool(ok),
            weights=[dict(row=names[j], weight=float(w[j]))
                     for j in range(len(w)) if w[j] > 1e-9],
            sup_atom=dict(rho=float(sup_nm[0]), phi=float(sup_nm[1]))))
    HERE.joinpath("segment_U_K%d.json" % K).write_text(
        json.dumps(out, indent=1), encoding="utf8")
    print("wrote segment_U_K%d.json" % K)


if __name__ == "__main__":
    main()
