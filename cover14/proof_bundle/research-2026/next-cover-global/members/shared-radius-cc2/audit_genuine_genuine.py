"""
GENUINE configuration test.

Build an actual planar configuration of the kind the certificate talks about:
  * central triangle (real cover triple) with circumcenter O and circumradius R,
  * for each edge (u_i,u_{i+1}) of that triangle a neighbour triangle with
    circumcenter A_i on the other side of the edge and circumradius <= U,
    sharing the chord u_i u_{i+1} exactly (so |A_i-u_i| = |A_i-u_{i+1}| = T_i).
Then:
  (1) the paired-facet quadrilateral is (u_i, A_i, u_{i+1}, O); compute its
      SIGNED area several ways and compare with 0.5*R*T_i*sin(beta_i) and with
      the unsigned area,
  (2) the identity  sum_i Quad_i = shoelace(u1,A1,u2,A2,u3,A3),
  (3) whether Quad_i <= 0 can happen (which would break "sum = sum of positive
      facet areas"),
  (4) the hexagon side lengths vs U and the cap 3sqrt3/2 U^2.
"""
import json
import numpy as np

PI = np.pi
out = {}


def circumcenter(pts):
    (x1, y1), (x2, y2), (x3, y3) = pts
    d = 2 * (x1 * (y2 - y3) + x2 * (y3 - y1) + x3 * (y1 - y2))
    if abs(d) < 1e-14:
        return None, None
    ux = ((x1 ** 2 + y1 ** 2) * (y2 - y3) + (x2 ** 2 + y2 ** 2) * (y3 - y1)
          + (x3 ** 2 + y3 ** 2) * (y1 - y2)) / d
    uy = ((x1 ** 2 + y1 ** 2) * (x3 - x2) + (x2 ** 2 + y2 ** 2) * (x1 - x3)
          + (x3 ** 2 + y3 ** 2) * (x2 - x1)) / d
    return np.array([ux, uy]), float(np.hypot(ux - x1, uy - y1))


def signed_area(poly):
    poly = np.asarray(poly, float)
    x, y = poly[:, 0], poly[:, 1]
    return 0.5 * float(np.sum(x * np.roll(y, -1) - np.roll(x, -1) * y))


def build(cover_pts, neighbour_pts, O=None):
    """cover_pts: 3 points of the central triangle; neighbour_pts[k]: a third
    point defining the neighbour triangle across edge k (the neighbour triangle
    contains that point and the two chord endpoints).  Returns dict."""
    P = np.asarray(cover_pts, float)
    if O is None:
        O, R = circumcenter(P)
    else:
        O = np.asarray(O, float)
        R = float(np.hypot(*(P[0] - O)))
    res = dict(O=O.tolist(), R=R)
    A = []
    for k in range(3):
        i, j = k, (k + 1) % 3
        tri = np.array([P[i], P[j], neighbour_pts[k]])
        Ak, Tk = circumcenter(tri)
        A.append(Ak)
        res[f'T{k}'] = Tk
    res['A'] = [a.tolist() for a in A]
    quads = []
    for k in range(3):
        i, j = k, (k + 1) % 3
        poly = np.array([P[i], A[k], P[j], O])
        quads.append(signed_area(poly))
    res['quad_signed'] = quads
    res['quad_sum'] = float(sum(quads))
    walk = []
    for k in range(3):
        walk.append(P[k]); walk.append(A[k])
    walk = np.array(walk)
    res['walk_order'] = 'u1,A1,u2,A2,u3,A3'
    res['shoelace'] = signed_area(walk)
    sl = [float(np.linalg.norm(walk[(k + 1) % 6] - walk[k])) for k in range(6)]
    res['side_lengths'] = sl
    res['side_max'] = max(sl)
    res['U'] = res['side_max']
    # beta_k: angle at O in the facet triangle (O, u_i, u_{i+1})
    betas = []
    for k in range(3):
        i, j = k, (k + 1) % 3
        v1, v2 = P[i] - O, P[j] - O
        betas.append(float(np.arccos(np.clip(np.dot(v1, v2) / (np.linalg.norm(v1) * np.linalg.norm(v2)), -1, 1))))
    res['beta'] = betas
    res['sum_beta'] = float(sum(betas))
    res['formula_0.5R T sin beta'] = [0.5 * R * res[f'T{k}'] * np.sin(betas[k]) for k in range(3)]
    # neighbor triangle areas (unsigned) and central area
    res['central_area'] = float(abs(signed_area(P)))
    res['neighbour_areas'] = [float(abs(signed_area(np.array([P[k], P[(k + 1) % 3], neighbour_pts[k]])))) for k in range(3)]
    return res


# --- the natural cover: unit circle, equilateral-ish triangles
cases = {}
# case 1: equilateral cover on unit circle, neighbours = unit triangles built
# on each side with the third point outside (circumradius <= 1)
ang = np.array([PI / 2, PI / 2 + 2 * PI / 3, PI / 2 + 4 * PI / 3])
P = np.stack([np.cos(ang), np.sin(ang)]).T
nb = []
for k in range(3):
    i, j = k, (k + 1) % 3
    M = 0.5 * (P[i] + P[j])
    outward = M / np.linalg.norm(M)          # away from O
    # third point at distance so the neighbour triangle has circumradius ~1
    for h in [np.sqrt(3) / 2, 1.0, 1.2]:
        pt = M + h * outward
        cc, rr = circumcenter(np.array([P[i], P[j], pt]))
        if rr is not None and rr <= 1 + 1e-9:
            nb.append(pt)
            break
    else:
        nb.append(M + 0.5 * outward)
cases['equilateral_cover_unit'] = build(P, nb)

# case 2: a thin cover triangle
P2 = np.array([[1.0, 0.0], [0.0, 1.0], [-0.8, -0.6]])
nb2 = []
for k in range(3):
    i, j = k, (k + 1) % 3
    M = 0.5 * (P2[i] + P2[j])
    out_dir = M / np.linalg.norm(M)
    pt = M + 0.7 * out_dir
    nb2.append(pt)
cases['thin_cover'] = build(P2, nb2)

# case 3: cover triangle with O outside (acute-angled case)
P3 = np.array([[1.0, 0.2], [0.1, 1.1], [-0.9, -0.4]])
nb3 = []
for k in range(3):
    i, j = k, (k + 1) % 3
    M = 0.5 * (P3[i] + P3[j])
    out_dir = M / np.linalg.norm(M)
    nb3.append(M + 0.6 * out_dir)
cases['acute_cover'] = build(P3, nb3)

out['cases'] = cases
print(json.dumps(out, indent=1)[:4000])
with open(r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\next-cover-global\members\shared-radius-cc2\genuine_genuine.json", 'w') as f:
    json.dump(out, f, indent=1)
