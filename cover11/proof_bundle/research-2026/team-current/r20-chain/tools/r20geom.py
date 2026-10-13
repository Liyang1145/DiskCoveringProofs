"""r20-chain tools: common geometry for the q0(6,7) two-hub class.

NO symmetry / equal-angle / saturation premise.  All formulas are exact statements about
Euclidean disks and are tested numerically before use.
"""
import io, json
import numpy as np
from pathlib import Path

HERE = Path(__file__).resolve().parent
OUT = HERE.parent / "out"
OBJ = HERE.parent.parent / "cline2-sharp-fan" / "out" / "certified_object_copy.json"


def load_certified():
    o = json.load(io.open(OBJ, encoding="utf-8"))
    C = np.array([[int(a) / 1e17, int(b) / 1e17] for a, b in o["centers_scaled_1e17"]])
    R = float(o["certified_interval"]["lo"])
    ring_ids = np.array([1, 3, 4, 5, 6, 7, 8, 9, 10])
    return C, R, ring_ids


def polar_order(pts):
    return np.argsort(np.arctan2(pts[:, 1], pts[:, 0]))


def circle_arc_isect_unit(C, R):
    """Intersection of circle Cc(C,R) with the closed unit disk, as an angular interval
    about C.  Returns (t_lo, t_hi) in [0,2pi) with the covered arc going CCW from t_lo to t_hi
    (i.e. |angle| <= alpha where angle measured from the 'near' direction -C/|C|).
    Returns None when empty or when the whole circle is inside the disk."""
    L = np.linalg.norm(C)
    disc = L * L + R * R - 1.0
    if disc <= 0.0:
        return None            # whole circle inside the unit disk
    if L >= 1.0 + R:
        return None            # disjoint
    a = (L * L + R * R - 1.0) / (2.0 * L)
    h = np.sqrt(max(R * R - a * a, 0.0))
    u = C / L                        # unit along C
    n = np.array([-u[1], u[0]])      # CCW normal
    x1 = a * u + h * n
    x2 = a * u - h * n
    t1 = np.arctan2(*(x1 - C)[::-1])
    t2 = np.arctan2(*(x2 - C)[::-1])
    # arc contained in D is the one through the pole direction (t=pi in the (u,n) frame)
    def is_inside(t):
        p = C + R * np.array([np.cos(t), np.sin(t)])
        return np.linalg.norm(p) <= 1.0 + 1e-15
    # walk from t1 CCW to t2 and back; pick the piece whose midpoint is inside
    d = (t2 - t1) % (2 * np.pi)
    tm = (t1 + d / 2) % (2 * np.pi)
    if is_inside(tm):
        return t1, t2
    return t2, t1


def arc_distance_range(P, Q, C, R):
    """[min,max] distance from the origin over the CCW arc of Cc(C,R) from angle(P) to angle(Q)."""
    tP = np.arctan2(*(P - C)[::-1])
    tQ = np.arctan2(*(Q - C)[::-1])
    d = (tQ - tP) % (2 * np.pi)
    # candidate extrema: endpoints, and the pole t = angle(-C) if on the arc
    cand = [np.linalg.norm(P), np.linalg.norm(Q)]
    tp = np.arctan2(*((-C)[::-1]))
    if ((tp - tP) % (2 * np.pi)) <= d + 1e-15:
        cand.append(abs(np.linalg.norm(C) - R))
    return min(cand), max(cand)


def s_H(H, c, R):
    """spoke deficit: s = arccos(|H-c|/(2R)); +inf when the spoke is longer than 2R."""
    d = np.linalg.norm(np.asarray(c) - H)
    return np.arccos(np.clip(d / (2 * R), -1, 1)) if d <= 2 * R else np.inf
