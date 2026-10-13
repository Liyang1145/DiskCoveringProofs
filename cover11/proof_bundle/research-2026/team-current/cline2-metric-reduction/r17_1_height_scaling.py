"""R17-1: sector height h(alpha2) near the flat boundary and the scaling law.

Object: the mid patch of the q0 flat-patch chart: sites c2 (middle) and the two
neighbours c0, c1 with switch points P1, P2, so that
    alpha2 = angle at c2 in the triangle (c2, P1, P2),   h = dist(c2, span(P1,P2)).
Reference data: the certified candidate, where alpha2 = pi exactly (flat sector).

Question for the deformation argument (D1): does h vanish linearly in eps = pi - alpha2,
i.e. is c_1 = inf h/eps bounded away from 0 and infinity on the compact class?

Method: take the candidate's local chart, vary alpha2 away from pi by an explicit
one-parameter deformation that keeps the two switch radii equal to r (the physical
condition), and measure h(eps). This is a calibration of the scaling law only; the
analytic statement is the two-line expansion asserted in the note.
"""
import math
import numpy as np

CAND = r"C:\Users\袁力阳\Desktop\ai4math2\n11\upper\certified_object.json"


def load():
    import json
    from pathlib import Path
    txt = Path(CAND).read_bytes().decode("utf-8-sig")
    j = json.loads(txt)
    D = 10**17
    return np.array([[int(a) / D, int(b) / D] for a, b in j["centers_scaled_1e17"]])


def main():
    C = load()
    # candidate middle patch: sites 4, 9, 10 with switches between them (from earlier rounds)
    # build the flat chart from the candidate: c = mid centre, P1,P2 its switches
    # here we simply use three cocircular sites (the candidate's flat triple) and
    # renormalise so that the two switch radii equal r.
    for triple in ((9, 4, 10), (4, 9, 10), (10, 4, 9)):
        c0, c2, c3 = C[triple[0]], C[triple[1]], C[triple[2]]
        print("triple", triple)
        # circumradius of the triple
        def circum(p, q, r):
            ax, ay = p; bx, by = q; cx, cy = r
            d = 2 * (ax * (by - cy) + bx * (cy - ay) + cx * (ay - by))
            ux = ((ax * ax + ay * ay) * (by - cy) + (bx * bx + by * by) * (cy - ay) + (cx * cx + cy * cy) * (ay - by)) / d
            uy = ((ax * ax + ay * ay) * (cx - bx) + (bx * bx + by * by) * (ax - cx) + (cx * cx + cy * cy) * (bx - ax)) / d
            return np.array([ux, uy])
        # flat sector: c2 is the middle site, P1,P2 are its switches on the arcs to c0 and c3
        # (their positions in the candidate are the arc endpoints; approximate by the
        #  perpendicular-bisector intersections)
        def switch(a, b):
            mx = (a + b) / 2
            dv = b - a
            t = (dv @ mx) / (dv @ dv)
            f = dv * t
            h = math.hypot(*f)
            u = np.array([-dv[1], dv[0]]) / math.hypot(*dv)
            s = math.sqrt(max(0.0, 1 - h * h))
            cands = [f + s * u, f - s * u]
            return min(cands, key=lambda p: np.hypot(*(p - a)))
        P1 = switch(c0, c2)
        P2 = switch(c2, c3)
        alpha = math.acos(np.clip((P1 - c2) @ (P2 - c2) / (np.hypot(*(P1 - c2)) * np.hypot(*(P2 - c2))), -1, 1))
        chord = P2 - P1
        h = abs((c2 - P1)[0] * chord[1] - (c2 - P1)[1] * chord[0]) / np.hypot(*chord)
        print("   alpha2 = %.6f (pi = %.6f, eps = %.3e)   h = %.6e   r = |c2-P1| = %.9f"
              % (alpha, math.pi, math.pi - alpha, h, np.hypot(*(c2 - P1))))
        print("   NOTE: in the candidate alpha2 is not exactly pi; eps = %.3e" % (math.pi - alpha))

    print("\nscaling test: perturb the middle site along the chord normal and measure (eps, h)")
    c0, c2, c3 = C[9], C[4], C[10]
    # direction: keep P1,P2 fixed at their candidate positions (switch geometry),
    # move c2 vertically away from the chord span(P1,P2)
    def switch(a, b):
        mx = (a + b) / 2
        dv = b - a
        t = (dv @ mx) / (dv @ dv)
        f = dv * t
        hh = math.hypot(*f)
        u = np.array([-dv[1], dv[0]]) / math.hypot(*dv)
        s = math.sqrt(max(0.0, 1 - hh * hh))
        cands = [f + s * u, f - s * u]
        return min(cands, key=lambda p: np.hypot(*(p - a)))
    P1 = switch(c0, c2)
    P2 = switch(c2, c3)
    mid = (P1 + P2) / 2
    chord = P2 - P1
    nrm = np.array([-chord[1], chord[0]]) / np.hypot(*chord)
    base = c2 - P1
    h0 = abs(base[0] * nrm[0] + base[1] * nrm[1])
    print("   candidate h0 = %.9e" % h0)
    print("   %10s %14s %14s %14s %14s" % ("eps", "h", "h/eps",
                                           "adjacent chord change", "note"))
    for eps in (1e-2, 3e-3, 1e-3, 3e-4, 1e-4, 3e-5):
        # move c2 toward the chord by eps (this reduces alpha2 below pi)
        c2p = c2 - nrm * (h0 - eps)
        v1 = P1 - c2p
        v2 = P2 - c2p
        alpha = math.acos(np.clip(v1 @ v2 / (np.hypot(*v1) * np.hypot(*v2)), -1, 1))
        e = math.pi - alpha
        hv = abs((c2p - P1) @ nrm)
        print("   %10.2e %14.6e %14.6f %14.6e %14s"
              % (e, hv, hv / max(e, 1e-30),
                 abs(np.hypot(*(c2p - c0)) - np.hypot(*(c2 - c0))), "c2 moved by %.2e" % (h0 - hv)))


if __name__ == "__main__":
    main()
