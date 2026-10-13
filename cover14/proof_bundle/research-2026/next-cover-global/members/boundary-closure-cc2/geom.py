"""Independent geometry kernel for the boundary-anchor closure audit (cc2).

Objects
-------
Disk D = unit disk centred at origin.  sites = array (n,2) of distinct interior sites.
Boundary ownership: J_i = {x in S1 : |x-c_i| <= |x-c_j| for all j}; anchors = points of S1
where the nearest-site label changes.

At an anchor A, the two owners are (u_cw, v_ccw) = (owner of the arc CW of A, owner of the arc
CCW of A).  Local frame at A: e_rho = -A (inward radial), e_t = (-A_y, A_x) (CCW tangent).
For a direction w (vector from A) write
    ang(w) = atan2( <w,e_rho>, <w,e_t> ) in (-pi,pi]
so ang=0 is the CCW tangent, ang=+90deg the inward radial, ang=pi the CW tangent.
Polygon interior sector at A = [theta_ccw/2, pi - theta_cw/2] (CCW order).

Reported per anchor
-------------------
  gam      : atan((|<uv|/2|)/|A-m|) -- angle between ray A->site and ray A->facet  (= angle at A
             of triangle (site,A,O));  gam<pi/2  <=>  h_A<0.
  ang_m    : ang(dir A->m) where m = midpoint of the two owners (m in int D); facet ray direction.
  phi_*    : cell interior angle at A on each side = ang_m resp. pi-ang_m; cone of the cell.
  nest_ccw : ang_m - gam - theta_ccw/2  (>0 <=> site ray strictly CCW of chord ray A->A_next)
  nest_cw  : (pi - ang_m) - gam - theta_cw/2
  resid    : 2*gam + delta_ccw + delta_cw + (theta_ccw+theta_cw)/2 - pi
             (zero iff both nesting slacks are >=0 with equality-free generic case)
  O_int    : the interior vertex closing the facet [A,O] (None if the facet runs to the other
             circle point -> full-chord case), |O|.
"""
import math
import numpy as np


def anchors_of(sites, M=600000):
    sites = np.asarray(sites, float)
    t = 2 * np.pi * np.arange(M) / M
    X = np.stack([np.cos(t), np.sin(t)], 1)
    D2 = ((X[:, None, :] - sites[None, :, :]) ** 2).sum(-1)
    own = D2.argmin(1)
    sw = np.nonzero(own != np.roll(own, 1))[0]
    out = []
    for k in sw:
        i, j = int(own[k - 1]), int(own[k])
        if i == j:
            continue
        lo, hi = t[k - 1], t[k]
        d = sites[j] - sites[i]
        ra = float(np.linalg.norm(d))
        if ra < 1e-13:
            continue
        b = float(sites[j] @ sites[j] - sites[i] @ sites[i]) / 2.0
        if abs(b) > ra:
            continue
        phi = math.atan2(d[1], d[0])
        c = math.acos(max(-1.0, min(1.0, b / ra)))
        for cand in (phi + c, phi - c):
            th = cand % (2 * np.pi)
            inside = (lo - 1e-9 <= th <= hi + 1e-9) if hi >= lo else (th >= lo - 1e-9 or th <= hi + 1e-9)
            if not inside:
                continue
            A = np.array([math.cos(th), math.sin(th)])
            dd = np.linalg.norm(sites - A, axis=1)
            order = list(np.argsort(dd)[:4])
            out.append(dict(t=th, A=A, pair=(i, j), order=order, dist=[float(dd[q]) for q in order]))
            break
    out.sort(key=lambda r: r["t"])
    return out


def ang_of(w, A):
    """signed angle of direction w measured at A (w is a vector, not a point)."""
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
    A = 2 * np.array([q - p, r - p])
    b = np.array([q @ q - p @ p, r @ r - p @ p])
    try:
        return np.linalg.solve(A, b)
    except np.linalg.LinAlgError:
        return None


def facet_end(sites, u, v, A, allsites=None):
    """First hit of the ray A -> m (m midpoint of u,v) with a third-site bisector.
    Returns (O, w) with O the circumcenter of (u,v,w) hit first, or None if the ray
    leaves the disk before any third site is met (full-chord/no-interior-vertex case)."""
    sites = np.asarray(sites, float)
    m = (sites[u] + sites[v]) / 2
    dirv = m - A
    nrm = np.linalg.norm(dirv)
    if nrm < 1e-15:
        return None
    dirv = dirv / nrm
    best = None
    for w in range(len(sites)):
        if w in (u, v):
            continue
        O = circumcenter(sites[u], sites[v], sites[w])
        if O is None:
            continue
        s = float((O - A) @ dirv)
        if s <= 1e-12:
            continue
        # O must lie on the line A + s dirv
        perp = np.linalg.norm((O - A) - s * dirv)
        if perp > 1e-7 * max(1.0, abs(s)):
            continue
        if best is None or s < best[2]:
            best = (O, w, s)
    if best is None:
        return None
    return best


def analyse(sites, M=600000, tag=""):
    sites = np.asarray(sites, float)
    n = len(sites)
    anch = anchors_of(sites, M)
    q = len(anch)
    recs = []
    # arc owner between consecutive anchors
    arcowner = []
    for k in range(q):
        p1, p2 = set(anch[k]["pair"]), set(anch[(k + 1) % q]["pair"])
        common = p1 & p2
        arcowner.append(sorted(common))
    for k, a in enumerate(anch):
        A = a["A"]
        u, v = a["pair"]
        # consistency: anchor owners == owners of the two adjacent arcs
        ow_cw = arcowner[(k - 1) % q]
        ow_ccw = arcowner[k]
        m = (sites[u] + sites[v]) / 2
        mu = np.linalg.norm(A - m)
        gam = math.atan2(float(np.linalg.norm(sites[v] - sites[u]) / 2), mu)
        ang_m = ang_of(m - A, A)
        # angles of the two site rays
        ang_u, ang_v = ang_of(sites[u] - A, A), ang_of(sites[v] - A, A)
        th_ccw = wrap(anch[(k + 1) % q]["t"] - a["t"]) % (2 * math.pi)
        th_cw = wrap(a["t"] - anch[(k - 1) % q]["t"]) % (2 * math.pi)
        Anext = anch[(k + 1) % q]["A"]
        Aprev = anch[(k - 1) % q]["A"]
        dir_next = wrap(ang_of(Anext - A, A))
        dir_prev = wrap(ang_of(Aprev - A, A))
        # delta's: triangle angles at A
        d_ccw = angle_between(sites[ow_ccw[0]] - A, Anext - A) if len(ow_ccw) == 1 else float("nan")
        d_cw = angle_between(Aprev - A, sites[ow_cw[0]] - A) if len(ow_cw) == 1 else float("nan")
        resid = 2 * gam + d_ccw + d_cw + (th_ccw + th_cw) / 2 - math.pi
        recs.append(dict(
            tag=tag, k=k, t=a["t"], pair=[u, v], owners_order=a["order"],
            nmargin=float(a["dist"][1] - a["dist"][2]) if len(a["dist"]) > 2 else None,
            mid_gap=float(a["dist"][1]),
            arc_cw=ow_cw, arc_ccw=ow_ccw,
            theta_ccw=th_ccw, theta_cw=th_cw,
            gam=gam, ang_m=ang_m, ang_u=ang_u, ang_v=ang_v,
            dir_next=dir_next, dir_prev=dir_prev,
            phi_ccw=ang_m, phi_cw=math.pi - ang_m,
            nest_ccw=ang_m - gam - th_ccw / 2,
            nest_cw=(math.pi - ang_m) - gam - th_cw / 2,
            delta_ccw=d_ccw, delta_cw=d_cw, resid=resid,
        ))
    return recs


def angle_between(x, y):
    nx, ny = np.linalg.norm(x), np.linalg.norm(y)
    if nx < 1e-15 or ny < 1e-15:
        return float("nan")
    c = float(x @ y) / (nx * ny)
    return math.acos(max(-1.0, min(1.0, c)))


def covering_radius(sites, G=400):
    """max over grid in closed unit disk of distance to nearest site (grid estimate)."""
    xs = np.linspace(-1, 1, G)
    X, Y = np.meshgrid(xs, xs)
    keep = X ** 2 + Y ** 2 <= 1.0
    P = np.stack([X[keep], Y[keep]], 1)
    d = np.linalg.norm(P[:, None, :] - np.asarray(sites)[None, :, :], axis=2)
    return float(d.min(1).max())
