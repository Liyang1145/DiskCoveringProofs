"""n12 -- explicit closed form of the K=1 one-hub dual functional.

The K=1 dual returned six nonzero rows:
  boundary_cos1_+1 = boundary_cos1_-1 = a   (moments cancel: 2a * t)
  hub_sin1_+1 = hub_sin1_-1 = b             (moments cancel: 2b * beta)
  hub_cos1_-1 = c                           (hub_cos1_+1 = 0)
so the functional is the explicit two-circle quantity

    F(rho,phi) = 2a * t(rho) + 2b * beta(c) - c * sin(beta(c)) * cos(psi(c)),

    t(rho)  = arccos((1 + rho^2 - R^2)/(2 rho)),      (S^1 arc half-width)
    c       = rho (cos phi, sin phi),  h = (e, 0),
    ell     = |c-h|,  psi = arg(c-h),
    beta    = arccos(min(1, ell/(2R)))                (arc on |x-h| = R+eps)

Certificate shape: if  F <= 1 + delta  for every centre in the annulus
rho in [1-R, 1+R], then  11 >= pi * sum(w) / (1+delta),  and sum(w) large
enough turns this into an exclusion of the k=11 structure at radius R.
This script only measures sup F numerically (fine grid) and prints the
coefficients; certification of the continuous sup is a separate step.
"""
import json
import sys
import numpy as np
from pathlib import Path

U = 0.361102963744508672616920293904
HERE = Path(__file__).parent


def F_of(rho, phi, e, a, b, c, R=U):
    rho = np.asarray(rho, float)
    phi = np.asarray(phi, float)
    t = np.arccos(np.clip((1.0 + rho * rho - R * R) / (2.0 * rho), -1, 1))
    cx = rho * np.cos(phi)
    cy = rho * np.sin(phi)
    ell = np.hypot(cx - e, cy)
    psi = np.arctan2(cy, cx - e)
    beta = np.arccos(np.minimum(1.0, ell / (2.0 * R)))
    return 2.0 * a * t + 2.0 * b * beta - c * np.sin(beta) * np.cos(psi)


def coeffs_from_json(path):
    d = json.load(open(path, encoding="utf8"))
    run = d["runs"][0] if "runs" in d else d
    w = {r["row"]: r["weight"] for r in run["weights"]}
    a = w.get("boundary_cos1_1", 0.0)
    a2 = w.get("boundary_cos1_-1", 0.0)
    b = w.get("hub_sin1_1", 0.0)
    b2 = w.get("hub_sin1_-1", 0.0)
    c = w.get("hub_cos1_-1", 0.0)
    return dict(a=a, a2=a2, b=b, b2=b2, c=c,
                other={k: v for k, v in w.items()
                       if k not in ("boundary_cos1_1", "boundary_cos1_-1",
                                    "hub_sin1_1", "hub_sin1_-1",
                                    "hub_cos1_-1")},
                sum_w=run.get("sum_weights"))


def sup_fine(e, coef, nr=4000, nphi=4000, R=U):
    a = 0.5 * (coef["a"] + coef["a2"])
    b = 0.5 * (coef["b"] + coef["b2"])
    c = coef["c"]
    best = (-1e9, None)
    rho = np.linspace(1.0 - R, 1.0 + R, nr)
    chunk = 200
    for i0 in range(0, nr, chunk):
        rr = rho[i0:i0 + chunk]
        Rr, Pp = np.meshgrid(rr, np.linspace(0, 2 * np.pi, nphi, endpoint=False),
                             indexing="ij")
        F = F_of(Rr, Pp, e, a, b, c, R)
        j = int(np.argmax(F))
        if F.ravel()[j] > best[0]:
            best = (float(F.ravel()[j]),
                    (float(Rr.ravel()[j]), float(Pp.ravel()[j])))
    return best, a, b, c


if __name__ == "__main__":
    path = sys.argv[1] if len(sys.argv) > 1 else str(HERE / "onehub_dual_U_e0.040.json")
    e = float(sys.argv[2]) if len(sys.argv) > 2 else 0.04
    coef = coeffs_from_json(path)
    print("coefficients from", path)
    print(json.dumps(coef, indent=1))
    (sup, arg), a, b, c = sup_fine(e, coef)
    print("folded coefficients: a=%.9f b=%.9f c=%.9f" % (a, b, c))
    print("numeric sup of F on 4000x4000 grid = %.9f at (rho,phi)=(%.6f,%.6f)"
          % (sup, arg[0], arg[1]))
    print("implied bound with delta = sup-1: pi*sum(w)/sup = %.6f"
          % (np.pi * coef["sum_w"] / sup))
