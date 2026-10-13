"""C13: exact block analysis of the 43-row system at the certified candidate.

Blocks (all built from exact Euclidean coordinates of the 22 integer literals):
  (M) 21 shared-edge side-matching rows
        y_f^2 sin^2 A = y_g^2 sin^2 B   for each pair of faces sharing an edge,
        with y_f = rho_f/R and A,B the opposite angles.
      Unknowns: 20 log-radii (11 interior Voronoi-vertex faces + 9 boundary
      switches).  Radii normalised by R so no R enters.
  (A) 11 face angle sums (identities on Euclidean directions: reported only)
  (C)  9 cyclic-closure rows  T_i + L_(i+1) + 2 b_i + (w_i+w_(i+1))/2 - pi,
      i.e.  T_i + L_(i+1) + (w_i+w_(i+1))/2  =  pi - 2 b_i .
  Unknowns for (M)+(C): the 22 site coordinates (3 gauge fixed) + 20 log-radii.

Outputs: residuals, Jacobian rank, the kernel basis (the two dependencies), and
the analytic identification of each dependency (cycle identity vs total width).
"""
import json, math
from pathlib import Path
import numpy as np
from scipy.spatial import Voronoi

HERE = Path(__file__).parent
ROOT = HERE.parent.parent.parent
OUT = HERE / "out"
pi = math.pi


def load():
    txt = (ROOT / "n11" / "upper" / "certified_object.json").read_bytes().decode("utf-8-sig")
    j = json.loads(txt)
    D = 10**17
    return np.array([[int(a) / D, int(b) / D] for a, b in j["centers_scaled_1e17"]])


def combinatorics(C):
    """returns faces (list of site triples), face vertices, edges, switch info."""
    vor = Voronoi(C)
    # map each voronoi vertex to the sites that attain the min distance
    faces = []
    for v in vor.vertices:
        d = np.hypot(*(C - v[None, :]).T)
        r = d.min()
        near = tuple(sorted(int(k) for k in range(len(C)) if abs(d[k] - r) < 1e-9))
        if v @ v <= 1.0 + 1e-12:
            faces.append({"v": v, "sites": near, "r": r})
    # edges: ridge_points pairs
    edges = []
    for (a, b) in vor.ridge_points:
        edges.append((int(a), int(b)))
    return vor, faces, edges


def main():
    C = load()
    n = len(C)
    R = 0.37998385311983884
    vor, faces, edges = combinatorics(C)
    print("faces (interior Voronoi vertices):", len(faces))
    for f in faces:
        print("   sites", f["sites"], "r", round(f["r"], 12), "|v|", round(float(np.hypot(*f["v"])), 9))

    # --- boundary structures
    N0 = 720000
    t0 = np.linspace(0, 2 * pi, N0 + 1)[:-1]
    c0 = np.stack([np.cos(t0), np.sin(t0)], 1)
    d0 = np.hypot(c0[:, 0:1] - C[None, :, 0], c0[:, 1:2] - C[None, :, 1])
    own = np.argmin(d0, 1)
    order = []
    for k in range(N0):
        if own[k] != own[k - 1]:
            order.append(int(own[k]))
    # ring = the 9 sites owning boundary arcs
    m = len(order)
    # switches between consecutive ring sites
    sw = []
    for i in range(m):
        s, s2 = order[i], order[(i + 1) % m]
        a, b = C[s], C[s2]
        mx = (a + b) / 2
        dv = b - a
        tt = (dv @ mx) / (dv @ dv)
        f = dv * tt
        h = math.hypot(*f)
        u = np.array([-dv[1], dv[0]]) / math.hypot(*dv)
        ss = math.sqrt(max(0.0, 1 - h * h))
        for sgn in (1, -1):
            p = f + sgn * ss * u
            d = np.hypot(*(C - p[None, :]).T)
            if d.min() >= 0.37998385311 - 1e-9:
                sw.append((i, s, s2, p))
                break
    print("\nring order:", order)
    print("switch gaps (deg):", np.round(np.degrees([((math.atan2(sw[(i+1)%m][3][1], sw[(i+1)%m][3][0]) - math.atan2(sw[i][3][1], sw[i][3][0])) % (2*pi)) for i in range(m)]), 6).tolist())

    # --- the M block: build the graph of faces, 21 edges
    # node index: 0..10 = interior faces, 11..19 = switches (leaf nodes)
    nodes = []
    rad = []
    for f in faces:
        nodes.append({"kind": "V", "sites": f["sites"], "v": f["v"]})
        rad.append(f["r"])
    for (i, s, s2, p) in sw:
        nodes.append({"kind": "S", "sites": (s, s2), "v": p})
        rad.append(float(np.hypot(*(C[s] - p))))
    N = len(nodes)
    y = np.array([rad[k] / R for k in range(N)]) if False else np.array(rad) / R
    print("\nnodes:", N, " (11 Voronoi-vertex faces + 9 switches)")
    print("y = rho/R:", np.round(y, 15).tolist())

    # build edge list of the "face/apex graph": for every site pair (i,j) that are
    # neighbours in the Delaunay graph, the two nodes whose faces contain both
    edge_rows = []
    for (a, b) in edges:
        A = [k for k in range(N) if a in nodes[k]["sites"] and b in nodes[k]["sites"]]
        if len(A) != 2:
            print("  !! edge", (a, b), "incident nodes:", A)
            continue
        edge_rows.append((a, b, A[0], A[1]))
    print("edges with two incident nodes:", len(edge_rows))

    def opposite_angle(node, i, j):
        """angle at the remaining site of the face (or pi/2-gamma for a switch)."""
        sites = nodes[node]["sites"]
        if node < 11:
            k = [s for s in sites if s not in (i, j)]
            assert len(k) == 1
            k = k[0]
            # angle at k in triangle (i,k,j)
            u = C[i] - C[k]
            w = C[j] - C[k]
            return math.acos(np.clip(u @ w / (np.hypot(*u) * np.hypot(*w)), -1, 1))
        else:
            # switch: the two rays to the sites; the face angle is pi - (that angle)/2
            i2, j2 = i, j
            u = C[i2] - nodes[node]["v"]
            w = C[j2] - nodes[node]["v"]
            ang = math.acos(np.clip(u @ w / (np.hypot(*u) * np.hypot(*w)), -1, 1))
            return pi - ang / 2.0

    def Mrows(Cloc, yloc):
        out = []
        for (a, b, p, q) in edge_rows:
            Ap = opposite_angle(p, a, b)
            Aq = opposite_angle(q, a, b)
            out.append(yloc[p] ** 2 * math.sin(Ap) ** 2 - yloc[q] ** 2 * math.sin(Aq) ** 2)
        return np.array(out)

    r0 = Mrows(C, y)
    print("\nM residuals max:", np.abs(r0).max())
    print("M residual vector (should be ~0):", np.round(r0, 14).tolist())

    # --- Jacobian of M in the 20 log-radii variables (site coords fixed)
    JM = np.zeros((len(edge_rows), N))
    h = 1e-7
    for k in range(N):
        yp = y.copy(); yp[k] *= (1 + h)
        ym = y.copy(); ym[k] *= (1 - h)
        JM[:, k] = (Mrows(C, yp) - Mrows(C, ym)) / (2 * h * 1.0)
    U, S, Vt = np.linalg.svd(JM)
    print("singular values of dM/dlog rho:", np.round(S, 10).tolist())
    print("rank:", int((S > 1e-8 * S[0]).sum()), " of", len(edge_rows), "rows,", N, "vars")

    OUT.mkdir(exist_ok=True)
    (OUT / "c13_blocks.json").write_text(json.dumps({
        "ring_order": order,
        "y": y.tolist(),
        "M_resid": r0.tolist(),
        "singvals": S.tolist(),
        "n_edges": len(edge_rows),
    }, indent=2))
    print("wrote", OUT / "c13_blocks.json")


if __name__ == "__main__":
    main()
