# -*- coding: utf-8 -*-
"""r20-alternative / calibration + weaker lower witness (self-contained): the reused C462 kernel on a ladder of t."""
import json, time
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent.parent
src = json.loads((ROOT / "n11" / "upper" / "certified_object.json").read_text(encoding="utf-8-sig"))
A = [tuple(F(int(x), 10 ** 17) for x in p) for i, p in enumerate(src["centers_scaled_1e17"]) if i not in (0, 2)]
R_down = F(3799838531, 10 ** 10); R_up = F(3799838532, 10 ** 10)
dot = lambda a, b: sum(x * y for x, y in zip(a, b))
sub = lambda a, b: tuple(x - y for x, y in zip(a, b))
sq = lambda a, b: dot(sub(a, b), sub(a, b))


def member_ok(p):
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
    al = (uu * vv - uv * vv) / (2 * det); be = (uu * vv - uv * uu) / (2 * det)
    return tuple(a[k] + al * u[k] + be * v[k] for k in (0, 1)), [1 - al - be, al, be]


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
    surv = 0
    for mask in range(1 << (n - 1)):
        if not any(mask & b == b or (full ^ mask) & b == b for b in bad):
            surv += 1
    return bad, certs, surv


core = [tuple(map(F, p)) for p in json.loads((ROOT / "research-2026" / "solo-20260922" / "auxiliary_hole_core.json").read_text())["points"]]
assert all(member_ok(p) for p in core), "core point failed exact membership"
print("core: %d points, all exact strict-hole at R_up; kernel ladder (reused C462 structure):" % len(core))
for name, T in [("0.379965", F(379965, 10 ** 6)), ("0.37997", F(37997, 100000)),
                ("0.379975", F(379975, 10 ** 6)), ("0.37998", F(37998, 100000)),
                ("0.3799825", F(3799825, 10 ** 7)), ("0.3799835", F(3799835, 10 ** 7)),
                ("0.3799837531 (= R_down-1e-7)", F(3799837531, 10 ** 10))]:
    st = time.time(); bad, certs, surv = search(core, T)
    print("   t = %-28s (%.10f)  forbidden=%3d  survivors=%-8d  %s   [%.1f s]"
          % (name, float(T), len(certs), surv, "UNSAT -> LOWER WITNESS" if surv == 0 else "(2-coverable at this radius)", time.time() - st))
    if surv == 0:
        out = {"status": "LOWER WITNESS", "points": len(core), "hub_test_radius": str(T), "hub_test_radius_float": float(T),
               "n_forbidden": len(certs), "forbidden_sets": certs, "point_set": [[str(x), str(y)] for x, y in core],
               "ring_radius_bounds": [str(R_down), str(R_up)],
               "inference": "P subset K (exact membership), no two radius-t disks cover P => rho2(K) > t"}
        (HERE / ("lower_witness_t_%.10f.json" % float(T))).write_text(json.dumps(out, indent=1), encoding="utf-8")
        print("      -> written lower_witness_t_%.10f.json" % float(T))
