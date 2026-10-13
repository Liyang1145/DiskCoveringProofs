"""r20-geometry: interface checks for C877 (split residual finite-vertex maximum theorem)
and R21-RESIDUAL-MEMBERSHIP.  Two explicit degenerate cases, no parameter sweeps.

Object: U = {x in D: |x-c_i| > r for all ring i}, K = closure_D(U),
        V(L) = {pairwise ring-circle intersections in S} U {L-intersections with a ring circle
                that belong to K},  S = K \cap {n.x <= t}.
Claim (C877): if S nonempty then V nonempty and max_{x in S}|x-h|^2 = max_{v in V}|v-h|^2.

(A) Equilateral isolated-equality trap (why the exact closure membership criterion is
    load-bearing, and in which direction the naive rule errs).
(B) Tangency calibration: an admissible ring family (distinct centres, |c_i| <= s, boundary
    covered) whose circle pair is exactly tangent at an interior point of K; compare the exact
    vertex maximum with a dense residual maximum for six splits and four hub positions.
    This is calibration only; the continuum statement is the analytic case analysis.
"""
import json, math, sys
from mpmath import mp, mpf, sin, cos, sqrt, asin, acos, pi as MP_PI

mp.dps = 40


# ---------------------------------------------------------------- (A) equilateral trap
def trap(r=mpf(1) / 2):
    C = [(r * cos(2 * MP_PI * k / 3), r * sin(2 * MP_PI * k / 3)) for k in range(3)]
    x0 = (mpf(0), mpf(0))


    def dsq(c, y):
        return (y[0] - c[0]) ** 2 + (y[1] - c[1]) ** 2


    dist = [sqrt(dsq(c, x0)) for c in C]
    v = [(x0[0] - c[0], x0[1] - c[1]) for c in C]
    # x in K  <=>  max_d min_i (v_i . d) >= 0     (v_i = x - c_i, d unit)
    def g(th):
        dd = (cos(th), sin(th))
        return min(vi[0] * dd[0] + vi[1] * dd[1] for vi in v)
    cover = max(g(2 * MP_PI * k / 2880) for k in range(2880))
    # pairwise circle intersections = points equidistant (= r) from both centres
    inter = []
    for i in range(3):
        for j in range(i + 1, 3):
            if (abs(sqrt(dsq(C[i], x0)) - r) < mpf("1e-30")
                    and abs(sqrt(dsq(C[j], x0)) - r) < mpf("1e-30")):
                inter.append(x0)
    return dict(centres=[[float(p) for p in c] for c in C], x0=[0.0, 0.0],
                distances=[mp.nstr(d, 20) for d in dist],
                naive_all_ge_r=all(abs(d - r) < mpf("1e-30") for d in dist),
                closure_criterion_accepts=(cover >= 0),
                punctured_ball_covered=(cover < 0),
                x0_is_pairwise_circle_intersection=len(inter) > 0)


print("== (A) equilateral isolated-equality trap ==")
A = trap()
print("   three centres at |c|=1/2, 120 deg apart, r=1/2;  distances to origin:",
      A["distances"])
print("   all distances >= r (naive K_N test)      :", A["naive_all_ge_r"])
print("   exact closure criterion accepts x0       :", A["closure_criterion_accepts"])
print("   punctured ball around x0 ring-covered    :", A["punctured_ball_covered"])
print("   x0 is a pairwise circle intersection     :", A["x0_is_pairwise_circle_intersection"])
print("   => x0 satisfies the naive >= test and IS a pairwise circle intersection, but is")
print("      NOT in K = closure(strictly-uncovered); the naive vertex rule adds it to V.\n")


# ---------------------------------------------------------------- (B) tangency calibration
def build_ring_family(r=mpf(1) / 2, rad=mpf(7) / 10, ndisk=8):
    C = [(rad * cos(2 * MP_PI * k / ndisk), rad * sin(2 * MP_PI * k / ndisk)) for k in range(ndisk)]
    return C, r, rad, 2 * MP_PI / ndisk


def coverage_gap(C, r):
    """half-width of the boundary arc covered by one disk:  analytic."""
    a = []
    for c in C:
        nc = sqrt(c[0] ** 2 + c[1] ** 2)
        ca = (1 + nc ** 2 - r ** 2) / (2 * nc)
        if ca > 1:
            a.append(0.0)
        else:
            a.append(float(acos(ca)))
    return a


C, r, rad, dl = build_ring_family()
print("== (B) finite-vertex calibration on an admissible ring family ==")
print("   %d disks, r=%.3f, |c|=%.3f, angular pitch=%.4f rad (=%.3f deg);  s=sqrt(1-r^2)=%.4f"
      % (len(C), float(r), float(rad), float(dl), float(dl * 180 / MP_PI),
         float(sqrt(1 - r * r))))
hw = coverage_gap(C, r)
print("   analytic boundary half-width per disk: %.4f deg (pitch/2 = %.4f deg) -> covered: %s"
      % (hw[0] * 180 / math.pi, float(dl) * 90 / math.pi, hw[0] >= dl / 2))
worst = max(min(math.hypot(math.cos(th) - c[0], math.sin(th) - c[1]) for c in C)
            for th in [2 * math.pi * k / 200000 for k in range(200000)])
print("   sampled max over boundary of nearest-ring distance = %.12f  (r=%.3f) -> covered: %s"
      % (worst, float(r), worst <= float(r) + 1e-12))


def dsq(c, y):
    return (y[0] - c[0]) ** 2 + (y[1] - c[1]) ** 2


def membership(x, tol=0):
    """exact closure criterion: x in K iff the active normals v_i = x - c_i lie in a closed
    semicircle, i.e. iff the maximal angular gap between consecutive active directions >= pi.
    (For finitely many directions this is exact; a tolerance only guards the >= pi equality.)"""
    d = [sqrt(dsq(c, x)) for c in C]
    if any(di < r - tol for di in d):
        return False
    act = [i for i in range(len(C)) if abs(d[i] - r) <= tol]
    if not act:
        return True
    ang = sorted(math.atan2(x[1] - C[i][1], x[0] - C[i][0]) % (2 * math.pi) for i in act)
    gaps = [ang[(k + 1) % len(ang)] - ang[k] for k in range(len(ang) - 1)]
    gaps.append(ang[0] + 2 * math.pi - ang[-1])
    return max(gaps) >= math.pi - 1e-9


# tangency of the separating LINE with a ring circle: take L tangent to circle k at its
# outward point (that point lies in K: it is outside every other disk of this family).
k = 0
outward = (rad * cos(0) + r, rad * sin(0))            # c_0 + r*(1,0)
n_tan = (mpf(1), mpf(0))
t_tan = outward[0]                                   # L: x = outward_x  (tangent to C_0)
print("   tangent line candidate: x = %.9f, tangent to C_0 at %.9f (|x|=%.6f)"
      % (float(t_tan), float(outward[0]), float(outward[0])))
print("   tangency point in K by the closure criterion :", membership(outward, mpf("1e-25")))


def vertices(n, t, members_only=True):
    """exact vertex list for split L: n.x = t  (V = circle-circle inside S  +  L-circle in K)."""
    L = lambda y: n[0] * y[0] + n[1] * y[1] - t
    V = []
    for i in range(len(C)):
        for j in range(i + 1, len(C)):
            ci, cj = C[i], C[j]
            d = sqrt(dsq(ci, cj))
            if d == 0 or d > 2 * r:
                continue
            u = ((cj[0] - ci[0]) / d, (cj[1] - ci[1]) / d)
            A_ = (d * d) / (2 * d)
            B_ = sqrt(max(mpf(0), r * r - A_ * A_))
            for sgn in ([1] if B_ == 0 else [1, -1]):
                p = (ci[0] + A_ * u[0] - sgn * B_ * u[1], ci[1] + A_ * u[1] + sgn * B_ * u[0])
                if p[0] ** 2 + p[1] ** 2 >= 1:            # K subset D
                    continue
                if L(p) <= 0 and (not members_only or membership(p, mpf("1e-25"))):
                    V.append(p)
    for c in C:                                  # line-circle intersections
        nrm = sqrt(n[0] ** 2 + n[1] ** 2)
        nn = (n[0] / nrm, n[1] / nrm)            # unit normal
        foot = (nn[0] * t, nn[1] * t) if abs(t) > 0 else (mpf(0), mpf(0))
        e = (-nn[1], nn[0])                      # unit direction along L
        w = (c[0] - foot[0], c[1] - foot[1])
        s0 = w[0] * e[0] + w[1] * e[1]
        perp2 = w[0] ** 2 + w[1] ** 2 - s0 ** 2
        disc = r * r - perp2
        if disc < 0:
            continue
        for sgn in ([0] if disc == 0 else [1, -1]):
            s = s0 + sgn * sqrt(disc)
            p = (foot[0] + s * e[0], foot[1] + s * e[1])
            if p[0] ** 2 + p[1] ** 2 >= 1:
                continue
            if L(p) <= 0 and membership(p, mpf("1e-25")):
                V.append(p)
    return V


def dense_max(n, t, h, N=400, M=400):
    """max of |x-h|^2 over a dense sample of S = K cap {n.x<=t}, then 2 local refinements."""
    best = None
    box = [(mpf(-1), mpf(1)), (mpf(-1), mpf(1))]
    for it in range(3):
        (x0, x1), (y0, y1) = box
        for i in range(N + 1):
            x = x0 + (x1 - x0) * mpf(i) / N
            for j in range(M + 1):
                y = y0 + (y1 - y0) * mpf(j) / M
                if x * x + y * y >= 1:
                    continue
                if n[0] * x + n[1] * y > t:
                    continue
                if not membership((x, y), mpf("1e-12")):
                    continue
                f = (x - h[0]) ** 2 + (y - h[1]) ** 2
                if best is None or f > best[0]:
                    best = (f, (x, y))
        if best is None:
            return None, None
        cx, cy = best[1]
        box = [(cx - (x1 - x0) / N, cx + (x1 - x0) / N), (cy - (y1 - y0) / M, cy + (y1 - y0) / M)]
    return best


print("\n   split line / hub comparisons  (max over V  vs  dense max over S):")
rows = []
n_diag = (mpf(1) / sqrt(2), mpf(1) / sqrt(2))
for tag, n, t, h in [
    ("x<=%.3f (tangent)" % float(t_tan), n_tan, t_tan, (mpf(0), mpf(0))),
    ("x>=%.3f (tangent)" % float(t_tan), n_tan, t_tan, C[0]),
    ("y<=0.1", (mpf(0), mpf(1)), mpf("0.1"), (mpf("0.2"), mpf("0.2"))),
    ("y<=0.45", (mpf(0), mpf(1)), mpf("0.45"), (mpf(0), mpf(0))),
    ("diag<=0.2", n_diag, mpf("0.2"), (mpf("0.1"), mpf("-0.3"))),
    ("x<=-0.05", (mpf(1), mpf(0)), mpf("-0.05"), (mpf("0.4"), mpf("0.1"))),
]:
    V = vertices(n, t)
    if V:
        fV = max((v[0] - h[0]) ** 2 + (v[1] - h[1]) ** 2 for v in V)
    else:
        fV = None
    fS, xs = dense_max(n, t, h)
    rows.append(dict(tag=tag, nV=len(V), maxV=None if fV is None else float(fV),
                     maxS=None if fS is None else float(fS),
                     diff=None if (fV is None or fS is None) else float(fS - fV)))
    print("     %-16s |V|=%2d  maxV=%s  maxS=%s  diff=%s"
          % (tag, len(V), "%.10f" % float(fV) if fV is not None else "empty",
             "%.10f" % float(fS) if fS is not None else "empty",
             "%+.2e" % float(fS - fV) if (fV is not None and fS is not None) else "-"))

json.dump(dict(trap=A, ring_family=dict(r=float(r), rad=float(rad), n_disks=len(C), rows=rows),
               line_tangency_point=[float(outward[0]), float(outward[1])]),
          open("review_r21_vertices.json", "w"), indent=1)
print("\nwrote review_r21_vertices.json")
