"""r20 THREE-TERMINAL CONTRACTION control (one short numeric control; no global scan).

Writes ../out/three_terminal_contraction.txt.  Read-only elsewhere.

MECHANISM (lead's obligation)
  In the 51-edge fixed-switch graph, take three anchors U_i,U_j,U_k and one common FREE node Z,
  with shortest path lengths m_i,m_j,m_k (edge counts).  Along each path every edge has length <= V,
  so the triangle inequality gives  |U_t - Z| <= m_t * V  for t = i,j,k.
  Hence, with the multiplicatively weighted 1-center
        W(U_i,U_j,U_k; m_i,m_j,m_k) := min_Z max_t |U_t - Z| / m_t ,
  we obtain the NECESSARY bound       V(U) >= W .
  (This is a path-contraction; it does NOT need a free node adjacent to three anchors, so the
   earlier "no Steiner/Y node" remark does not kill it.)
  Control below enumerates the finite set (common free node, anchor triple) -- a bounded
  combinatorial search, not a grid -- and reports the best bound, the achieving tree, and the
  comparison with the best single two-edge bound.
"""
import json, collections, itertools
from pathlib import Path
import numpy as np
from scipy.optimize import minimize

ROOT = Path(__file__).resolve().parents[3]
OUT = Path(__file__).resolve().parent.parent / "out"
LOG = []


def P(*a):
    s = " ".join(str(x) for x in a)
    print(s)
    LOG.append(s)


def weighted_center(pts, ms):
    """min_Z max_t |U_t - Z| / m_t  (convex, 3 points)."""
    A = np.vstack(pts)

    def f(z):
        return float(np.max(np.linalg.norm(A - z, axis=1) / ms))
    best = 1e9
    for z0 in [A.mean(axis=0)] + [A[t] for t in range(3)] + [A[t]*0.5 for t in range(3)]:
        r = minimize(f, z0, method='Nelder-Mead',
                     options=dict(xatol=1e-12, fatol=1e-14, maxiter=4000))
        best = min(best, float(r.fun))
    return best


def main():
    E = json.loads((ROOT / "team-current/r20-alternative/socp_anchor_export.json").read_text())
    inc = E["incidence_map"]
    U = np.array(E["U"], float)
    R = float(E.get("R_star", E["r_solution"]))
    edges = []
    for (kind, site, q) in inc:
        edges.append((9 + int(site), int(q)) if kind == "endpoint" else (9 + int(site), 20 + int(q)))
    adj = collections.defaultdict(set)
    for v, w in edges:
        adj[v].add(w); adj[w].add(v)

    def bfs(s):
        d = {s: 0}; Q = collections.deque([s])
        while Q:
            u = Q.popleft()
            for w in adj[u]:
                if w not in d:
                    d[w] = d[u]+1; Q.append(w)
        return d
    dist = {a: bfs(a) for a in range(9)}
    free_nodes = [18, 19] + list(range(20, 31))     # hub a, hub b, 11 aux nodes

    P("=" * 96)
    P("THREE-TERMINAL CONTRACTION control (numeric proposal; bounded enumeration, no grid)")
    P("graph: %d edges ; anchors 0..8 ; common free nodes considered: hubs 18,19 + aux 20..30" % len(edges))
    P("R* = %.15f ; best single two-edge bound at candidate = %.6f" % (R, None) if False else
      "R* = %.15f" % R)

    th = [float(np.arctan2(U[i][1], U[i][0])) for i in range(9)]
    gaps = [((th[(i+1) % 9]-th[i]) % (2*np.pi)) for i in range(9)]
    best_pair = float(max(np.sin(g/2) for g in gaps))
    P("candidate: gaps max = %.6f ; best single two-edge bound = %.6f ; R* = %.6f"
      % (max(gaps), best_pair, R))

    rows = []
    for Z in free_nodes:
        d = dist
        for (i, j, k) in itertools.combinations(range(9), 3):
            ms = []
            ok = True
            for a in (i, j, k):
                if Z not in d[a]:
                    ok = False; break
                ms.append(d[a][Z])
            if not ok:
                continue
            w = weighted_center(U[[i, j, k]], np.array(ms, float))
            rows.append((w, Z, (i, j, k), tuple(ms)))
    rows.sort(reverse=True)
    P("")
    P("best three-terminal bounds (top 6 of %d (node,triple) combinations):" % len(rows))
    for w, Z, tri, ms in rows[:6]:
        P("   Z=node%-3d anchors%s  m=%s  W = %.6f   (%s best pair ; %s R*)"
          % (Z, tri, ms, w,
             ">" if w > best_pair else "<=",
             ">" if w > R else "<="))
    P("")
    w0, Z0, tri0, ms0 = rows[0]
    P("chosen tree: common node Z = node %d ; anchors %s ; path lengths m = %s" % (Z0, tri0, ms0))
    P("  necessary bound  V >= W = %.9f  vs best single pair %.9f  vs R* %.9f" % (w0, best_pair, R))
    P("  stronger than single pair: %s ; exceeds R*: %s" % (w0 > best_pair, w0 > R))

    # uniform-gap calibration (all gaps 2pi/9)
    Ug = np.array([[np.cos(2*np.pi*t/9), np.sin(2*np.pi*t/9)] for t in range(9)], float)
    rowsg = []
    for Z in free_nodes:
        for (i, j, k) in itertools.combinations(range(9), 3):
            if all(Z in dist[a] for a in (i, j, k)):
                ms = tuple(dist[a][Z] for a in (i, j, k))
                rowsg.append((weighted_center(Ug[[i, j, k]], np.array(ms, float)), Z, (i, j, k), ms))
    rowsg.sort(reverse=True)
    wg, Zg, trig, msg = rowsg[0]
    P("")
    P("uniform-gap calibration (Delta = 2pi/9): best W = %.9f at Z=node %d anchors %s m=%s"
      % (wg, Zg, trig, msg))
    P("   uniform single two-edge bound = %.9f ; W > it: %s ; W > R*: %s"
      % (float(np.sin(np.pi/9)), wg > float(np.sin(np.pi/9)), wg > R))
    P("")
    P("SCOPE: float, numeric proposal only; finite enumeration over (free node, anchor triple); the")
    P("bound V >= W is necessary and analytic (path contraction + weighted 1-center); no family dies.")
    (OUT / "three_terminal_contraction.txt").write_text("\n".join(LOG) + "\n")
    P("wrote " + str(OUT / "three_terminal_contraction.txt"))


if __name__ == "__main__":
    main()
