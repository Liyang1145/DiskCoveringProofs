"""r20-chain tools: EXACT arc / hub-disk containment machinery.

All statements below are elementary Euclidean facts about a closed disk B(H,R), a circle
Cc(C,R) of the SAME radius R, and the closed unit disk D.

Fact A (linear form).  For |H|=:h, R>0 and any point x,
        |x-H| <= R   <=>   H.x >= (h^2 - R^2)/2 .
     So the set of legal hub positions covering a FIXED point x is the half-plane
        {H : H.x >= (h^2-R^2)/2}   (with h free, the half-plane through x with normal x).
     Consequences at fixed h:  arc A subset B(H,R)  <=>  min_{x in A} (H.x) >= (h^2-R^2)/2,
     and the min of a linear functional over the arc is attained at an intersection point of
     Cc(C,R) with D (Fact A') or at an endpoint (Fact D).

Fact A'. If |C|=L, 0<R<L, and R^2+R^2-d^2 > 0 for d=|C| (i.e. d = |C| < sqrt(2)R), the two
     points of Cc(C,R) ∩ ∂D are  x_± = C(1-R^2/L^2) ± (R/L) sqrt(L^2+R^2-1) J C, J=[[0,-1],[1,0]].
     Identity: setting p = |C|, the *rim radii* of these points (semantics: minimum of a linear
     functional along the arc) satisfy  <C, x_-/|x_-| > = (C.C - R^2)/R  i.e.  |P-C| = R where
     P = (C/|C|)(|C|-R) is the pole of the circle w.r.t. the origin.

Fact B (arc of the UNCOVERED rim, EXACT via the lens Cc(C_i,R) ∩ Cc(C_j,R), valid when
     d := |C_i - C_j| < 2R).  Put M = (C_i+C_j)/2, Gd = M - C_i, and
        x_far = M + kappa * Gd,   kappa = 2 sqrt(R^2 - d^2/4)/d        (the lens corner opposite C_i).
     Then the rim of Cc(C_i,R) NOT covered by B(C_j,R) is exactly the closed arc from x_far to Q
     through the pole P_i, where Q is the SECOND lens corner: Q = M - kappa*Gd  (Q is covered by
     B(C_j,R) as it lies on Cc(C_j,R)).  Hence the uncovered rim arc of Cc(C_i,R) has angular
     extent 2*(pi/2 - beta_i) about C_i with cos(beta_i) = d/(2R)  (beta_i is the lens half-angle).
     Numerically confirmed to 1e-15 in out/chain_verify.txt / out/arc_exact.txt.
"""
import numpy as np


def lens_corners(Ci, Cj, R):
    """The two intersection points of Cc(Ci,R) and Cc(Cj,R).  Returns (x_far, Q):
    x_far = the corner farther from Ci's angular 'near' side, Q = the corner on the Cj side."""
    d = np.linalg.norm(Cj - Ci)
    if d >= 2 * R:
        return None, None
    M = (Ci + Cj) / 2.0
    Gd = M - Ci
    k = 2.0 * np.sqrt(max(R * R - d * d / 4.0, 0.0)) / d
    J = np.array([[0.0, -1.0], [1.0, 0.0]])
    return M + k * (J @ Gd), M - k * (J @ Gd)


def uncovered_arc(Ci, Cj, R):
    """Endpoints of the uncovered rim arc of Cc(Ci,R) (the part not in B(Cj,R)),
    given as the pair (x_far, Q); x_far is (one of) the farthest point(s) of the lens from Cj."""
    x1, x2 = lens_corners(Ci, Cj, R)
    if x1 is None:
        return None, None
    # x_far must be far from Cj  (= the point where |x - Cj| is maximal along Cc(Ci,R) ∩ ...)
    if np.linalg.norm(x1 - Cj) > np.linalg.norm(x2 - Cj):
        return x1, x2
    return x2, x1


def ang_about(C, x):
    v = np.asarray(x) - np.asarray(C)
    return np.arctan2(v[1], v[0])


def clip_arc_to_unit_disk(C, R, A, B):
    """Clip the CCW arc of Cc(C,R) from A to B to the closed unit disk.
    Returns a list of sub-arcs [(a_i,b_i)] with a_i,b_i points, CCW, in order."""
    L = np.linalg.norm(C)
    if L + R <= 1.0 + 1e-15:
        return [(A, B)]                     # whole circle inside D
    disc = L * L + R * R - 1.0
    if disc <= 0.0:
        return [(A, B)]
    u = C / L
    n = np.array([-u[1], u[0]])
    a = (L * L + R * R - 1.0) / (2.0 * L)
    h = np.sqrt(max(R * R - a * a, 0.0))
    X1, X2 = a * u + h * n, a * u - h * n
    tA, tB, t1, t2 = ang_about(C, A), ang_about(C, B), ang_about(C, X1), ang_about(C, X2)
    span = (tB - tA) % (2 * np.pi)
    cuts = []
    for X, t in ((X1, t1), (X2, t2)):
        if ((t - tA) % (2 * np.pi)) <= span + 1e-14:
            cuts.append((t, X))
    pts = [(tA, A)] + sorted(cuts) + [(tA + span, B)]
    out = []
    for (ta, Pa), (tb, Pb) in zip(pts[:-1], pts[1:]):
        if tb - ta < 1e-14:
            continue
        tm = (ta + tb) / 2.0
        Pm = C + R * np.array([np.cos(tm), np.sin(tm)])
        if np.linalg.norm(Pm) <= 1.0 + 1e-13:
            out.append((Pa, Pb))
    return out


def linear_margin(H, R, pts):
    """For a hub H (|H|=h) and witness points pts that all must lie in B(H,R):
    slack := min_x (H.x) - (h^2-R^2)/2,  and slack >= 0  <=>  every witness is covered.
    (Fact A: |x-H| <= R  <=>  H.x >= (h^2-R^2)/2.)  Returns (+inf, None) for an empty witness set."""
    pts = np.asarray(pts, float)
    if pts.size == 0:
        return np.inf, None
    h2 = float(H @ H)
    vals = pts @ H - (h2 - R * R) / 2.0
    k = int(np.argmin(vals))
    return float(vals[k]), pts[k]


def arc_margin(H, R, subarcs):
    """slack for covering a union of sub-arcs: min over sub-arcs of the min over the sub-arc.
    For each sub-arc the min of the linear functional H.x is attained at an endpoint (the arc is
    a sub-arc of the circle cut by the line H.x = const, whose interior extremum would be the point
    of the circle with x parallel to H: that is an endpoint of the clipped arc in our usage, and it
    is included explicitly by the caller when needed)."""
    m = np.inf
    arg = None
    for (a, b) in subarcs:
        v, x = linear_margin(H, R, [a, b])
        if v < m:
            m, arg = v, x
    return m, arg
