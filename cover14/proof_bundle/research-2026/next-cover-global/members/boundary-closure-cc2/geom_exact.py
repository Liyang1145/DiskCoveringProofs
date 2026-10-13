"""Exact anchor enumeration + nesting-slack audit kernel (cc2).

anchors_exact: no sampling.  For every unordered pair (i,j) solve |x-c_i|=|x-c_j| on S1
analytically; keep x iff the pair is strictly nearest there (no third-site tie) -- then x is a
genuine ownership switch of owners {i,j} (nearestness gives a neighbourhood in which i,j are the
two nearest sites and the bisector crosses, so the label changes transversally).

anchor_record: all quantities of the closure interface at one anchor.
"""
import math
import numpy as np


def anchors_exact(sites, tie_tol=1e-9):
    sites = np.asarray(sites, float)
    n = len(sites)
    res = []
    for i in range(n):
        for j in range(i + 1, n):
            d = sites[j] - sites[i]
            ra = float(np.linalg.norm(d))
            if ra < 1e-14:
                continue
            b = float(sites[j] @ sites[j] - sites[i] @ sites[i]) / 2.0
            if abs(b) > ra:
                continue
            phi = math.atan2(d[1], d[0])
            c = math.acos(max(-1.0, min(1.0, b / ra)))
            for cand in (phi + c, phi - c):
                th = cand % (2 * math.pi)
                A = np.array([math.cos(th), math.sin(th)])
                dd = np.linalg.norm(sites - A, axis=1)
                order = list(np.argsort(dd))
                if not (i in order[:2] and j in order[:2]):
                    continue
                if dd[order[1]] - dd[order[0]] > 1e-9:
                    continue  # i,j not really tied -> not a crossing point
                if dd[order[2]] - dd[order[1]] < tie_tol:
                    continue  # third-site tie: degenerate anchor
                res.append(dict(t=th, A=A, pair=(int(order[0]), int(order[1])),
                                order=[int(x) for x in order[:4]],
                                dist=[float(dd[x]) for x in order[:4]]))
                break
    # dedupe (same t)
    res.sort(key=lambda r: r["t"])
    out = []
    for r in res:
        if out and abs(r["t"] - out[-1]["t"]) < 1e-12:
            continue
        out.append(r)
    return out


def ang_of(w, A):
    e_rho = -A
    e_t = np.array([-A[1], A[0]])
    return math.atan2(float(w @ e_rho), float(w @ e_t))


def wrap(x):
    while x > math.pi:
        x -= 2 * math.pi
    while x <= -math.pi:
        x += 2 * math.pi
    return x


def circumcenter(p, q, r):
    M = 2 * np.array([q - p, r - p])
    b = np.array([q @ q - p @ p, r @ r - p @ p])
    try:
        return np.linalg.solve(M, b)
    except np.linalg.LinAlgError:
        return None


def anchor_records(sites, M=None):
    """Returns list of records in CCW anchor order with all audit quantities."""
    sites = np.asarray(sites, float)
    anch = anchors_exact(sites)
    q = len(anch)
    recs = []
    for k in range(q):
        a = anch[k]
        A = a["A"]
        u, v = a["pair"]
        p1, p2 = set(a["pair"]), set(anch[(k + 1) % q]["pair"])
        common_ccw = sorted(p1 & p2)
        p0 = set(anch[(k - 1) % q]["pair"])
        common_cw = sorted(p0 & p1)
        m = (sites[u] + sites[v]) / 2
        gam = math.atan2(float(np.linalg.norm(sites[v] - sites[u]) / 2), float(np.linalg.norm(A - m)))
        ang_m = ang_of(m - A, A)
        ang_u = ang_of(sites[u] - A, A)
        ang_v = ang_of(sites[v] - A, A)
        th_ccw = float((anch[(k + 1) % q]["t"] - a["t"]) % (2 * math.pi))
        th_cw = float((a["t"] - anch[(k - 1) % q]["t"]) % (2 * math.pi))
        Anext, Aprev = anch[(k + 1) % q]["A"], anch[(k - 1) % q]["A"]
        d_ccw = angdiff(Anext - A, sites[common_ccw[0]] - A) if len(common_ccw) == 1 else float("nan")
        d_cw = angdiff(sites[common_cw[0]] - A, Aprev - A) if len(common_cw) == 1 else float("nan")
        resid = 2 * gam + d_ccw + d_cw + (th_ccw + th_cw) / 2 - math.pi
        # facet closure
        dirv = (m - A)
        dirv = dirv / np.linalg.norm(dirv)
        best = None
        for w in range(len(sites)):
            if w in (u, v):
                continue
            O = circumcenter(sites[u], sites[v], sites[w])
            if O is None:
                continue
            s = float((O - A) @ dirv)
            if s <= 0:
                continue
            if np.linalg.norm((O - A) - s * dirv) > 1e-7 * max(1.0, s):
                continue
            if best is None or s < best[2]:
                best = (O, w, s)
        recs.append(dict(
            k=k, t=a["t"], A=A, pair=[u, v], order=a["order"], nmargin=float(a["dist"][2] - a["dist"][1]),
            arc_ccw=common_ccw, arc_cw=common_cw, theta_ccw=th_ccw, theta_cw=th_cw,
            gam=gam, ang_m=ang_m, ang_u=ang_u, ang_v=ang_v,
            nest_ccw=ang_m - gam - th_ccw / 2, nest_cw=(math.pi - ang_m) - gam - th_cw / 2,
            delta_ccw=d_ccw, delta_cw=d_cw, resid=resid,
            facet=best,
            sym_err=abs(abs(ang_u - ang_m) - gam) + abs(abs(ang_v - ang_m) - gam),
            sites_norm_max=float(np.max(np.linalg.norm(sites, axis=1))),
            gap=float(min(np.linalg.norm(sites[p] - sites[r]) for p in range(len(sites)) for r in range(p)) ) if len(sites) > 1 else 0.0,
        ))
    return recs, anch


def angdiff(x, y):
    """undirected angle between vectors x,y in [0,pi]."""
    nx, ny = np.linalg.norm(x), np.linalg.norm(y)
    if nx < 1e-15 or ny < 1e-15:
        return float("nan")
    return math.acos(max(-1.0, min(1.0, float(x @ y) / (nx * ny))))


def covering_radius(sites, G=300):
    xs = np.linspace(-1, 1, G)
    X, Y = np.meshgrid(xs, xs)
    keep = X ** 2 + Y ** 2 <= 1.0
    P = np.stack([X[keep], Y[keep]], 1)
    d = np.linalg.norm(P[:, None, :] - np.asarray(sites)[None, :, :], axis=2)
    return float(d.min(1).max())
