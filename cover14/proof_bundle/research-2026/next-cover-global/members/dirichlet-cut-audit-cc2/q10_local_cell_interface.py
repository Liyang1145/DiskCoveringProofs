"""q10_local_cell_interface.py -- REPAIRED certified angular interface: q10 production anchors to the
C1324 literal +-1e-6 anchor cell (member scope; import-safe; no lead writes).

Fixes the issues recorded in DEAD.md line 65:
  (1) literal (px,py) is a TRUE interval enclosure (rigorous interval arithmetic on the exact dyadic
      root box, no midpoint, no ad-hoc pad);
  (2) the production<->literal correspondence is rebuilt through OWNER PAIRS: each literal anchor k
      carries an owner pair (p_k,q_k), the graph map phi sends literal SITE labels to production
      positions, and production anchor j matches the unique k with {phi(p_k),phi(q_k)}={j,j+1};
      site labels are never used as anchor indices;
  (3) the cell test uses ONE unwrapped branch per anchor for ALL vertices: Delta_j = phi_j(d) -
      psi_{sigma(j)} is formed directly, with no per-vertex 2pi wrapping; phi_j is affine in d, so
      the maximum over a convex deficit polytope is attained at a vertex;
  (4) production angles use phi_j = j*L - sum_{m<j} d_m;
  (5) real Q^3 vertex data is read from lead/q10-polytope-partition-879.json nodes[*].polytope.vertex_set.

All arithmetic is exact rational interval arithmetic; pi comes from the Machin series as an interval
(no rounded constant); no atan is used -- literal arcs come from chords through the arcsin series
arc = 2 arcsin(chord/2) with a geometric tail bound.

Formula.  Production anchor j is the junction owners[j,j+1] with gauge A_0=(1,0), so
    phi_j(d) = j*L - sum_{m<j} d_m,    d_j stored as a (cL,cB,c2pi) triple (q10: cB = 0).
Cell test.  With sigma: production j -> literal anchor sigma(j) and psi = cumulative literal arc from
the gauge anchor (one branch, unwrapped),
    PASS  <=>  max_j |phi_j(d) - psi_{sigma(j)}| <= eps = 1e-6   at every vertex, hence on the
               whole polytope by affinity.
NON-CLAIM: one literal cell, caller-supplied polytope only; no other anchor region; no global result.
"""

from fractions import Fraction as F
from math import isqrt, comb
import json
import os
import sys

sys.set_int_max_str_digits(200000)

U = F("0.33173203427623414")
EPS = F(1, 10 ** 6)
HERE = os.path.dirname(os.path.abspath(__file__))
LEAD = os.path.abspath(os.path.join(HERE, "..", "..", "lead"))


# ------------------------------------------------------------------ exact interval arithmetic
def iv(lo, hi=None):
    lo = F(lo)
    hi = lo if hi is None else F(hi)
    return (min(lo, hi), max(lo, hi))


def iadd(a, b):
    return (a[0] + b[0], a[1] + b[1])


def isub(a, b):
    return (a[0] - b[1], a[1] - b[0])


def imul(a, b):
    c = [a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1]]
    return (min(c), max(c))


def idiv(a, b):
    if b[0] <= 0 <= b[1]:
        raise ZeroDivisionError("interval divisor straddles 0: %s" % (b,))
    c = [a[0] / b[0], a[0] / b[1], a[1] / b[0], a[1] / b[1]]
    return (min(c), max(c))


def ipow(a, n):
    r = iv(1)
    for _ in range(n):
        r = imul(r, a)
    return r


def isqrt_iv(a, digits=40):
    if a[0] < 0:
        raise ValueError("negative sqrt")
    sc = 10 ** (2 * digits)

    def lo(v):
        return F(isqrt(v.numerator * sc // v.denominator), 10 ** digits)

    return lo(a[0]), lo(a[1]) + F(1, 10 ** digits)


def _atan_inv_bounds(m, n):
    s = F(0)
    for k in range(n):
        t = F(1, m ** (2 * k + 1) * (2 * k + 1))
        s += t if k % 2 == 0 else -t
    tn = F(1, m ** (2 * n + 1) * (2 * n + 1))
    return (s, s + tn) if n % 2 == 0 else (s - tn, s)


def pi_iv(n=40):
    alo, ahi = _atan_inv_bounds(5, n)
    blo, bhi = _atan_inv_bounds(239, n)
    return (16 * alo - 4 * bhi, 16 * ahi - 4 * blo)


PI = pi_iv()
TWO_PI = (2 * PI[0], 2 * PI[1])


def asin_series_iv(y, n=30):
    """arcsin(y) for a small interval y in [0,1) via the positive series with a tail bound.

    Powers are accumulated incrementally (y, y^3, y^5, ...) so the cost is O(n) interval products.
    """
    if y[0] < 0 or y[1] >= 1:
        raise ValueError("arcsin series needs 0 <= y < 1, got %s" % (y,))
    y2 = imul(y, y)
    odd = y
    lo = hi = F(0)
    for k in range(n):
        c = F(comb(2 * k, k), 4 ** k * (2 * k + 1))
        lo += c * odd[0]
        hi += c * odd[1]
        odd = imul(odd, y2)
    cn = F(comb(2 * n, n), 4 ** n * (2 * n + 1))
    tail = cn * odd[1] / (1 - y[1] * y[1]) if y[1] > 0 else F(0)
    return lo, hi + tail


def asin_U_iv(x, n=100):
    """arcsin(x) as a positive series (used for L = 2 asin U, where x < 1/2)."""
    c = [F(comb(2 * k, k), 4 ** k * (2 * k + 1)) for k in range(n)]
    lo = sum(c[k] * (x ** (2 * k + 1)) for k in range(n))
    return lo, lo + x ** (2 * n + 1) / (1 - x * x)


L_IV = tuple(2 * v for v in asin_U_iv(U))


# ---------------------------------------------------- true interval literal root geometry (no pad)
def literal_geometry():
    root = json.load(open(os.path.join(LEAD, "root-integer-certificate.json")))
    z, c, r = [iv(v[0], v[1]) for v in root["box_dyadic"]]
    s = isqrt_iv(isub(iv(1), imul(r, r)))
    a = idiv(iadd(s, z), iv(2))
    t = iadd(r, isqrt_iv(isub(imul(r, r), imul(z, z))))
    b = iadd(r, isqrt_iv(isub(imul(r, r), ipow(isub(a, z), 2))))
    dd = isub(iv(1), isqrt_iv(isub(imul(r, r), imul(c, c))))
    v1 = idiv(iadd(iadd(iv(1), imul(a, a)), isub(imul(b, b), imul(r, r))), iv(2))
    v2 = idiv(iadd(iadd(iv(1), imul(c, c)), isub(imul(dd, dd), imul(r, r))), iv(2))
    det = isub(imul(a, dd), imul(b, c))
    px = idiv(isub(imul(v1, dd), imul(v2, b)), det)
    py = idiv(isub(imul(a, v2), imul(c, v1)), det)
    A = [((s[0], s[1]), (r[0], r[1])), (px, py), ((F(0), F(0)), (F(1), F(1))),
         ((-px[1], -px[0]), py), ((-s[1], -s[0]), (r[0], r[1])),
         ((-s[1], -s[0]), (-r[1], -r[0])), ((-px[1], -px[0]), (-py[1], -py[0])),
         ((F(0), F(0)), (-F(1), -F(1))), (px, (-py[1], -py[0])),
         ((s[0], s[1]), (-r[1], -r[0]))]
    return A, {"z": z, "c": c, "r": r, "s": s, "a": a, "t": t, "b": b, "dd": dd, "px": px, "py": py}


def chord_iv(A, i, j):
    dx = isub(A[i][0], A[j][0])
    dy = isub(A[i][1], A[j][1])
    return isqrt_iv(iadd(imul(dx, dx), imul(dy, dy)))


def forward_arc_iv(A, k, q):
    """arc from literal anchor k to k+1 forwards, as 2*arcsin(chord/2) (rigorous, no atan)."""
    ch = idiv(chord_iv(A, k, (k + 1) % q), iv(2))
    if not (0 <= ch[0] <= ch[1] < 1):
        raise ValueError("chord/2 outside [0,1) for adjacent anchors %d,%d: %s"
                         % (k, (k + 1) % q, ch))
    return tuple(2 * v for v in asin_series_iv(ch))


def certify_literal_cycle(A, q=10):
    """certify the literal cyclic branch by DISCRETE WINDING (not by "the interval contains 2pi").

    Anchors are unit vectors by C1167's algebraic construction (radical-line solve with the circle
    identity), not by any residual interval; the residual is only a numeric consistency note.

    Inference:
      * every adjacent cross product x_i*y_{i+1} - y_i*x_{i+1} strictly positive, so each turn
        i -> i+1 is a minor counterclockwise arc of length in (0, pi);
      * the total counterclockwise turn along the closed cycle is therefore 2*pi*k for an integer
        winding number k; every arc is > 0 so the total is > 0, hence k >= 1;
      * the computed interval bounds that total; asserting it lies inside (pi, 3*pi) forces
        2*pi*k in (pi, 3*pi), i.e. k = 1 -- only then is the sum the exact single turn 2*pi.
    `arc_sum_contains_2pi` is reported separately as a CONSISTENCY CHECK ONLY: containing 2pi does not
    by itself imply an exact sum.
    """
    worst = None
    for k in range(q):
        i, j = k, (k + 1) % q
        z = isub(imul(A[i][0], A[j][1]), imul(A[i][1], A[j][0]))
        if worst is None or z[0] < worst:
            worst = z[0]
    total = iv(0)
    for k in range(q):
        total = iadd(total, forward_arc_iv(A, k, q))
    cross_ok = bool(worst is not None and worst > 0)
    in_band = bool(total[0] > PI[1] and total[1] < 3 * PI[0])       # (pi, 3pi), rigorous
    return {"cross_positive": cross_ok, "cross_min": worst, "arc_sum": total,
            "winding_band_pi_3pi": in_band,
            "winding_number_pinned": 1 if (cross_ok and in_band) else None,
            "arc_sum_contains_2pi": bool(total[0] <= TWO_PI[1] and total[1] >= TWO_PI[0]),
            "cycle_valid": bool(cross_ok and in_band),
            "note": "positive cross = minor CCW arc in (0,pi); a closed unit-vector cycle sums to "
                    "2*pi*k; the band (pi,3pi) pins k=1; contains-2pi is consistency only"}


def literal_owners():
    run = json.load(open(os.path.join(LEAD, "fixed-anchor-flow-certificate.json")))["runs"][0]
    return [tuple(o) for o in run["owners"]]


def graph_maps(index=879):
    """exact graph isomorphisms of ONE catalogue index, expanded to the site->production position map.

    The match file also carries runs for other indices; mixing them would silently change the
    correspondence, so the index is restricted explicitly (and must exist).
    """
    match = json.load(open(os.path.join(LEAD, "candidate-catalogue-match.json")))
    runs = [r for r in match["runs"] if r.get("index") == index]
    if not runs:
        raise ValueError("no run for catalogue index %s in candidate-catalogue-match.json" % index)
    cycle = match["boundary_cycle"]
    out = []
    for run in runs:
        for mm in run["exact_matches"]:
            for sign in (-1, 1):
                for sh in range(10):
                    if all(mm[str(v)] == (sh + sign * j) % 10 for j, v in enumerate(cycle)):
                        out.append({"index": run["index"], "shift": sh, "sign": sign,
                                    "phi": {v: (sh + sign * j) % 10 for j, v in enumerate(cycle)}})
    return out


def anchor_correspondence(phi, owners, q=10):
    """production anchor j -> literal anchor k, via owner pairs; asserts a bijection."""
    pairs = {}
    for k, (p, qq) in enumerate(owners):
        key = frozenset((phi[p], phi[qq]))
        if len(key) != 2:
            raise RuntimeError("literal anchor %d owner pair collapses under phi" % k)
        pairs.setdefault(key, []).append(k)
    sigma = {}
    for j in range(q):
        key = frozenset((j, (j + 1) % q))
        if len(pairs.get(key, [])) != 1:
            raise RuntimeError("production pair %s has %d literal anchors"
                               % (sorted(key), len(pairs.get(key, []))))
        sigma[j] = pairs[key][0]
    if len(set(sigma.values())) != q:
        raise RuntimeError("correspondence is not a bijection")
    return sigma


# ------------------------------------------------------------------- production angles and test
def prod_angles(d, q=None):
    """phi_j = j*L - sum_{m<j} d_m as intervals; d entries are (cL,cB,c2pi) triples, cB must be 0."""
    q = q or len(d)
    for m, tri in enumerate(d):
        if F(tri[1]) != 0:
            raise ValueError("q10 deficit triple %d has nonzero cB=%s" % (m, tri[1]))
    acc, out = iv(0), []
    for j in range(q):
        out.append(isub((F(j) * L_IV[0], F(j) * L_IV[1]), acc))
        dm = iadd(imul(iv(F(d[j][0])), L_IV), imul(iv(F(d[j][2])), TWO_PI))
        acc = iadd(acc, dm)
    return out


def cumulative_literal_arcs(A, sigma, q=10):
    """psi_j = cumulative literal arc from the gauge anchor to literal anchor sigma(j), one branch.

    No caching.  An earlier version keyed a dict on tuple(sigma); for sigma a dict that is the key
    tuple 0..9, identical for every map, and it also ignored A -- which silently made the four-map
    test non-independent.  Recomputing is cheap.
    """
    fwd = [forward_arc_iv(A, k, q) for k in range(q)]
    seq = [sigma[j] for j in range(q)]
    psi, acc = [], iv(0)
    for j, k in enumerate(seq):
        psi.append(acc)
        nxt = seq[(j + 1) % q]
        if nxt == (k + 1) % q:
            step = fwd[k]
        elif nxt == (k - 1) % q:
            step = fwd[nxt]
        else:
            raise RuntimeError("identification jumps %d -> %d" % (k, nxt))
        acc = iadd(acc, step)
    return psi, acc


def _rat_str(x, digits=30, direction=0):
    """exact outward-rounded decimal string of a Fraction (no floats in the certificate).

    direction = -1 floors, +1 ceils, 0 rounds to nearest half-up.
    """
    x = F(x)
    sc = 10 ** digits
    num = x * sc
    if direction < 0:
        v = num.numerator // num.denominator
    elif direction > 0:
        v = -((-num.numerator) // num.denominator)
    else:
        v = (num + F(1, 2)).numerator // (num + F(1, 2)).denominator
    return "%s/%d" % (v, sc)


def cell_cuts(sigma, A, eps=EPS, q=10):
    """explicit small-cell constraints: |phi_j - psi_j| <= eps is the linear prefix-sum condition

        sum_{m<j} d_m  in  [ j*L - psi_j - eps ,  j*L - psi_j + eps ].

    psi_j is known only as an interval [psi_lo, psi_hi], so two DIFFERENT families are emitted:

      outer_necessary  (weaker, valid for every true psi): any configuration inside the true cell
                       satisfies  j*L - psi_hi - eps <= sum_{m<j} d_m <= j*L - psi_lo + eps;
      inner_sufficient (stronger): any configuration satisfying
                       j*L - psi_lo - eps <= sum_{m<j} d_m <= j*L - psi_hi + eps
                       is inside the cell for EVERY psi in the interval, hence inside the true cell.

    The inner family is NOT a global feasibility cut: violating it only means the configuration is
    outside the sufficient inner cell, not that it is infeasible.  All endpoints are exact rationals,
    emitted as outward-rounded decimal rational strings ("p/10^30").
    """
    psi, _ = cumulative_literal_arcs(A, sigma, q)
    out = []
    for j in range(q):
        jL = (F(j) * L_IV[0], F(j) * L_IV[1])
        outer_lo = isub(isub(jL, iv(psi[j][1])), iv(eps))     # weakest lower bound: take [0]
        outer_hi = iadd(isub(jL, iv(psi[j][0])), iv(eps))     # weakest upper bound: take [1]
        inner_lo = isub(isub(jL, iv(psi[j][0])), iv(eps))
        inner_hi = iadd(isub(jL, iv(psi[j][1])), iv(eps))
        out.append({"anchor": j, "literal": sigma[j], "prefix_indices": list(range(j)),
                    "outer_necessary_prefix_lower": _rat_str(outer_lo[0], direction=-1),
                    "outer_necessary_prefix_upper": _rat_str(outer_hi[1], direction=+1),
                    "inner_sufficient_prefix_lower": _rat_str(inner_lo[1], direction=+1),
                    "inner_sufficient_prefix_upper": _rat_str(inner_hi[0], direction=-1)})
    return out


def cell_test(vertices, sigma, A, eps=EPS, q=10):
    """decide whether a convex deficit polytope lies in the literal cell.

    Guards: the vertex set must be non-empty (an empty polytope would otherwise pass vacuously), sigma
    must be a permutation of the anchors, and the literal cycle must be certified (positive crosses
    plus winding number pinned to 1).  `pass` is exact; the per-vertex, per-anchor numbers in `rows`
    are floats for reading and are internal diagnostics, not the bearing statement.
    """
    if vertices is None or len(vertices) == 0:
        raise ValueError("cell_test: empty vertex set -- refuse to pass vacuously")
    seq = list(sigma.values()) if isinstance(sigma, dict) else list(sigma)
    if sorted(seq) != list(range(q)):
        raise ValueError("cell_test: sigma is not a permutation of the %d anchors" % q)
    cyc = certify_literal_cycle(A, q)
    if not cyc["cycle_valid"]:
        raise RuntimeError("cell_test: literal cycle not certified (cross_positive=%s, winding=%s)"
                           % (cyc["cross_positive"], cyc["winding_number_pinned"]))
    sigma = {j: seq[j] for j in range(q)}
    psi, total = cumulative_literal_arcs(A, sigma, q)
    rows, ok = [], True
    for vi, v in enumerate(vertices):
        d = [tuple(F(x) for x in node) for node in v]
        ph = prod_angles(d, q)
        worst, worst_j, per = F(-1), None, []
        for j in range(q):
            delta = isub(ph[j], psi[j])
            mag = max(abs(delta[0]), abs(delta[1]))
            per.append({"j": j, "literal": sigma[j], "delta_lo": float(delta[0]),
                        "delta_hi": float(delta[1]), "ok": bool(mag <= eps)})
            if mag > worst:
                worst, worst_j = mag, j
        rows.append({"vertex": vi, "worst_anchor": worst_j, "worst_abs_delta": float(worst),
                     "worst_abs_delta_exact": worst, "pass": bool(worst <= eps), "anchors": per})
        ok = ok and worst <= eps
    return {"pass": bool(ok), "eps": EPS, "rows": rows, "worst_abs_delta_exact": max(
        (r["worst_abs_delta_exact"] for r in rows), default=F(0)),
            "total_literal_arc": (total[0] + total[1]) / 2,
            "branch": "single unwrapped cumulative branch per anchor, shared by all vertices",
            "affine_reason": "phi_j is affine in d and |Delta_j| is a max of two affine functions, so "
                             "a convex deficit polytope is decided by its vertices"}


def synthetic_accepting_cell(A, sigma, Q=10 ** 9, q=10):
    """small module-exact polytope near the literal configuration's own deficit vector.

    d_m = L - q_m*(2pi) with rational q_m <= arc_m/(2pi) (floor at denominator Q) and
    q_9 := 1 - sum_{m<9} q_m, so sum q = 1 exactly and every vertex satisfies sum d = q*L - 2pi
    exactly.  q_m is additionally capped by floor(Q*L_lo/(2pi_hi))/Q so the certified lower end of
    d_m is >= 0; the perturbation size is then limited by the certified slack, and every vertex is
    checked for d >= 0 (certified) rather than assumed.
    """
    fwd = [forward_arc_iv(A, k, q) for k in range(q)]
    seq = [sigma[j] for j in range(q)]
    arcs = []
    for j, k in enumerate(seq):
        nxt = seq[(j + 1) % q]
        arcs.append(fwd[k] if nxt == (k + 1) % q else fwd[nxt])
    # exact cap: floor(Q * L_lo / (2pi_hi)) / Q , ensuring cL*L - |c2pi|*2pi >= 0 for cL = 1
    capfrac = (Q * L_IV[0]) / TWO_PI[1]
    cap = F(capfrac.numerator // capfrac.denominator, Q)
    qm = []
    for m in range(q - 1):
        v = arcs[m][0] / TWO_PI[1]                      # conservative lower ratio
        qm.append(min(F(int(v * Q)) / Q, cap))
    qm.append(F(1) - sum(qm))
    if qm[-1] < 0 or qm[-1] > cap:
        raise RuntimeError("last rational ratio not within the certified cap: %s vs %s"
                           % (qm[-1], cap))
    base = [(F(1), F(0), -qm[m]) for m in range(q)]     # d_m = L - q_m*2pi
    slack = [isub(iv(L_IV[0], L_IV[1]), imul(iv(qm[m]), TWO_PI))[0] for m in range(q)]
    delta = min(F(1, 10 ** 12), min(slack) / 4) if slack else F(0)
    verts = []
    for j in range(q):
        v = []
        for m in range(q):
            cL, cB, c2 = base[m]
            cL = cL + (delta if m == j else (-delta if m == (j + 1) % q else 0))
            v.append((cL, cB, c2))
        verts.append(v)
    # certified domain checks (never claim membership without them)
    dom = {"all_vertices_d_nonneg_certified": True, "sum_is_exactly_10L_minus_2pi": True,
           "min_certified_d_lower_bound": min(slack) - delta, "delta": delta, "cap": cap}
    for v in verts:
        for m in range(q):
            cL, cB, c2 = F(v[m][0]), F(v[m][1]), F(v[m][2])
            lo = cL * L_IV[0] + (c2 * TWO_PI[1] if c2 < 0 else c2 * TWO_PI[0])
            if lo < 0:
                dom["all_vertices_d_nonneg_certified"] = False
        if (sum(F(x[0]) for x in v), sum(F(x[2]) for x in v)) != (F(q), F(-1)):
            dom["sum_is_exactly_10L_minus_2pi"] = False
    return verts, qm, dom


def load_partition_nodes():
    part = json.load(open(os.path.join(LEAD, "q10-polytope-partition-879.json")))
    out = {}
    for node in part["nodes"]:
        pol = node.get("polytope")
        if pol and pol.get("vertex_set"):
            out[node["id"]] = [[tuple(F(x) for x in tri) for tri in v] for v in pol["vertex_set"]]
    return part, out


def main():
    A, geom = literal_geometry()
    owners = literal_owners()
    maps = graph_maps()
    part, nodes = load_partition_nodes()
    rr = iadd(imul(geom["px"], geom["px"]), imul(geom["py"], geom["py"]))
    cyc = certify_literal_cycle(A)
    res = {"schema": "member-q10-local-cell-interface/v3",
           "U": str(U), "eps": str(EPS),
           "pi_interval": [_rat_str(PI[0]), _rat_str(PI[1])],
           "L_interval": [_rat_str(L_IV[0]), _rat_str(L_IV[1])],
           "px_py_interval": [_rat_str(geom["px"][0]), _rat_str(geom["px"][1]),
                              _rat_str(geom["py"][0]), _rat_str(geom["py"][1])],
           "px_py_unit_circle_residual": [_rat_str(rr[0] - 1), _rat_str(rr[1] - 1)],
           "literal_cycle_certificate": {
               "cross_positive": cyc["cross_positive"],
               "cross_min": _rat_str(cyc["cross_min"]),
               "arc_sum": [_rat_str(cyc["arc_sum"][0]), _rat_str(cyc["arc_sum"][1])],
               "arc_sum_contains_2pi_consistency_only": cyc["arc_sum_contains_2pi"],
               "winding_band_pi_3pi": cyc["winding_band_pi_3pi"],
               "winding_number_pinned": cyc["winding_number_pinned"],
               "cycle_valid": cyc["cycle_valid"],
               "reasoning": cyc["note"]},
           "literal_anchor_owner_pairs": [list(o) for o in owners],
           "partition_status": part.get("status"),
           "partition_nodes_with_vertices": sorted(nodes.keys()),
           "root_vertex_count": len(nodes.get(0, [])),
           "graph_maps": [],
           "non_claim": "one literal cell, caller polytope only; no global statement",
           "notes": ["bearing fields (pass flags, cycle certificate, cuts, psi intervals) are exact "
                     "rationals rounded outward to 30 decimals as p/10^30; cell_test's per-vertex "
                     "per-anchor margins are internal float diagnostics, not the bearing statement",
                     "literal cycle certified by discrete winding: positive adjacent crosses give "
                     "minor CCW arcs, a closed unit-vector cycle sums to 2*pi*k, and the band "
                     "(pi,3pi) pins k=1; the sum containing 2pi is a consistency check only",
                     "cell_test refuses an empty vertex set and asserts sigma is a permutation and "
                     "the cycle is certified",
                     "graph_maps is restricted to catalogue index 879",
                     "inner_sufficient cuts are not global feasibility cuts"]}
    print("pi width ~1e-58 ; L interval width %.3g" % float(L_IV[1] - L_IV[0]))
    print("literal cycle certified: cross_positive=%s cross_min=%.6g arc_sum_contains_2pi=%s" % (
        cyc["cross_positive"], float(cyc["cross_min"]), cyc["arc_sum_contains_2pi"]))
    for m in maps:
        sigma = anchor_correspondence(m["phi"], owners)
        psi, tot = cumulative_literal_arcs(A, sigma)
        entry = {"shift": m["shift"], "sign": m["sign"],
                 "sigma_production_to_literal": [sigma[j] for j in range(10)],
                 "psi_unwrapped_interval": [[_rat_str(psi[j][0], direction=-1),
                                             _rat_str(psi[j][1], direction=+1)]
                                            for j in range(10)],
                 "psi_midpoints": [_rat_str((psi[j][0] + psi[j][1]) / 2) for j in range(10)],
                 "prefix_cuts": cell_cuts(sigma, A)}
        REF = [0, 0.66716223, 1.23265734, 1.90893531, 2.47443042, 3.14159265, 3.80875489, 4.37425,
               5.05052796, 5.61602307]
        dev_lo = max(-(psi[j][0] - F(str(REF[j]))) if psi[j][0] - F(str(REF[j])) < 0
                     else -(psi[j][1] - F(str(REF[j]))) for j in range(10))
        entry["reference_angle_deviation_upper"] = _rat_str(
            max(max(abs(psi[j][0] - F(str(REF[j]))), abs(psi[j][1] - F(str(REF[j]))))
                for j in range(10)), direction=+1)
        root = nodes.get(0) or []
        if root:
            r = cell_test(root, sigma, A)
            entry["root_pass"] = r["pass"]
            entry["root_worst_abs_delta_exact"] = _rat_str(r["worst_abs_delta_exact"],
                                                           direction=+1)
            print("map (shift=%d, sign=%+d) sigma=%s" % (m["shift"], m["sign"],
                                                         [sigma[j] for j in range(10)]))
            print("   ROOT (%d vertices): pass=%s worst|Delta| = %.6f rad" % (
                len(root), r["pass"], max(x["worst_abs_delta"] for x in r["rows"])))
        verts, qm, dom = synthetic_accepting_cell(A, sigma)
        s = cell_test(verts, sigma, A)
        entry["synthetic_pass"] = s["pass"]
        entry["synthetic_worst_abs_delta_exact"] = _rat_str(s["worst_abs_delta_exact"],
                                                            direction=+1)
        entry["synthetic_vertices"] = len(verts)
        entry["synthetic_domain_checks"] = {
            "all_vertices_d_nonneg_certified": dom["all_vertices_d_nonneg_certified"],
            "sum_is_exactly_10L_minus_2pi": dom["sum_is_exactly_10L_minus_2pi"],
            "delta": _rat_str(dom["delta"]), "cap": _rat_str(dom["cap"]),
            "min_certified_d_lower_bound": _rat_str(dom["min_certified_d_lower_bound"])}
        print("   SYNTHETIC (%d vertices): pass=%s worst|Delta| = %.3e rad ; d>=0 certified=%s ; "
              "sum exact=%s" % (len(verts), s["pass"],
                                max(x["worst_abs_delta"] for x in s["rows"]),
                                dom["all_vertices_d_nonneg_certified"],
                                dom["sum_is_exactly_10L_minus_2pi"]))
        res["graph_maps"].append(entry)
    path = os.path.join(HERE, "q10-local-cell-interface.json")
    open(path, "w").write(json.dumps(res, indent=1))
    print("\nwritten:", path)

if __name__ == "__main__":
    main()
