# -*- coding: utf-8 -*-
"""
r20-alternative / prune-retry for the finite two-disk lower witness (≤20 points).

Pool = C462 deletion-core (19 strict-hole points) + the K-verified closure violators found by
finite_lower_witness.py. For each single deletion of a core point (giving 20 points = 18 core + 2
violators), rerun the EXACT forbidden-set Boolean search at t = R_down - 1e-7 and report UNSAT or
the number of survivors. If some 20-point set is UNSAT -> LOWER WITNESS (rho2(K) > t).
No line-direction grid; the only numeric choice is which verified K-points to include.
"""
import json, time
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent.parent
START = time.time()
R_down = F(3799838531, 10 ** 10); R_up = F(3799838532, 10 ** 10); T = F(3799837531, 10 ** 10)
src = json.loads((ROOT / "n11" / "upper" / "certified_object.json").read_text(encoding="utf-8-sig"))
A = [tuple(F(int(x), 10 ** 17) for x in p) for i, p in enumerate(src["centers_scaled_1e17"]) if i not in (0, 2)]
dot = lambda a, b: sum(x * y for x, y in zip(a, b))
sub = lambda a, b: tuple(x - y for x, y in zip(a, b))
sq = lambda a, b: dot(sub(a, b), sub(a, b))


def member_ok(p):
    """exact K-membership sufficient test: |p|<1, every ring dist^2 >= R_down^2, <=2 active rings."""
    if sq(p, (0, 0)) >= 1:
        return False
    if any(sq(p, a) < R_down * R_down for a in A):
        return False
    return sum(1 for a in A if sq(p, a) <= R_up * R_up) <= 2


def circumcentre(a, b, c):
    u, v = sub(b, a), sub(c, a)
    uu, uv, vv = dot(u, u), dot(u, v), dot(v, v)
    det = uu * vv - uv * uv
    if det == 0:
        return None, None
    alpha = (uu * vv - uv * vv) / (2 * det); beta = (uu * vv - uv * uu) / (2 * det)
    O = tuple(a[k] + alpha * u[k] + beta * v[k] for k in (0, 1))
    return O, [1 - alpha - beta, alpha, beta]


def forbidden_sets(P, t):
    n = len(P); bad = []; certs = []
    for i, k in combinations(range(n), 2):
        m = sq(P[i], P[k]) - 4 * t * t
        if m > 0:
            bad.append((1 << i) | (1 << k)); certs.append({"kind": "pair", "idx": [i, k], "margin": str(m)})
    for ids in combinations(range(n), 3):
        mask = sum(1 << i for i in ids)
        if any(mask & b == b for b in bad):
            continue
        a, b, c = [P[i] for i in ids]
        O, ws = circumcentre(a, b, c)
        if O is None or min(ws) < 0:
            continue
        mu = tuple(sum(w * P[i][k] for w, i in zip(ws, ids)) for k in (0, 1))
        V = sum(w * sq(P[i], mu) for w, i in zip(ws, ids))
        Rc2 = sq(O, a)
        if V > t * t:
            bad.append(mask); certs.append({"kind": "triple-variance", "idx": list(ids), "margin": str(V - t * t)})
        elif Rc2 > t * t:
            bad.append(mask); certs.append({"kind": "triple-circumcircle", "idx": list(ids), "margin": str(Rc2 - t * t)})
    return bad, certs


def search(P, t):
    n = len(P); bad, certs = forbidden_sets(P, t); full = (1 << n) - 1
    surv = 0; first = None
    for mask in range(1 << (n - 1)):
        if not any(mask & b == b or (full ^ mask) & b == b for b in bad):
            surv += 1
            if first is None:
                first = mask
    return bad, certs, surv, first


core = [tuple(map(F, p)) for p in json.loads((ROOT / "research-2026" / "solo-20260922" / "auxiliary_hole_core.json").read_text())["points"]]
# the two K-verified violators found by finite_lower_witness.py (ring-ring closure vertices, exact 12-digit rationals)
viol = [(F(220697611427, 10 ** 12), F(582510611965, 10 ** 12)),
        (F(-574102353, 10 ** 12), F(-529412040654, 10 ** 12))]
print("violators verified in K:", [member_ok(v) for v in viol])
CORE = core
assert all(member_ok(p) for p in CORE)

results = []
for drop in range(len(CORE)):
    P = [p for i, p in enumerate(CORE) if i != drop] + viol
    assert len(P) == 20 and all(member_ok(p) for p in P)
    bad, certs, surv, first = search(P, T)
    results.append((drop, surv, len(certs)))
    print("  drop core[%2d] -> n=%d forbidden=%d survivors=%d  (%.1f s)" % (drop, len(P), len(certs), surv, time.time() - START))
    if surv == 0:
        out = {"status": "LOWER WITNESS", "points": 20, "hub_test_radius": str(T),
               "ring_radius_bounds": [str(R_down), str(R_up)], "dropped_core_index": drop,
               "n_forbidden": len(certs), "forbidden_sets": certs,
               "point_set": [[str(x), str(y)] for x, y in P]}
        (HERE / "finite_lower_witness_pruned.json").write_text(json.dumps(out, indent=1), encoding="utf-8")
        print("\n*** LOWER WITNESS: 20-point UNSAT set at t=%.10f => rho2(K) > t ***" % float(T))
        raise SystemExit(0)
best = min(results, key=lambda z: z[1])
print("\nno 20-point UNSAT set found by single-deletion pruning; best survivors=%d at drop=%d" % (best[1], best[0]))
(HERE / "finite_lower_witness_pruned.json").write_text(json.dumps(
    {"status": "INSUFFICIENT", "hub_test_radius": str(T), "single_deletion_results": results}, indent=1), encoding="utf-8")
print("elapsed %.1f s" % (time.time() - START))
