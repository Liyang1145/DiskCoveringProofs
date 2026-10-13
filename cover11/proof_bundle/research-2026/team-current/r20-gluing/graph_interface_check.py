# -*- coding: utf-8 -*-
"""graph_interface_check.py — INDEPENDENT verification of the graph-interface items the lead asked
about, with my own code (no shared helpers):

 (1) counterexample: three equal-radius disks can share a point while the triangle's CIRCUMRADIUS
     exceeds r (obtuse case) => the clause "each facet noncollinear Rc <= r" is false as stated;
     the correct facet condition is the shared-point / MEC <= r form used by the bearing files.
 (2) independent re-enumeration of the two combinatorial lemmas cited in
     flash-structure/AUDIT-HUB-EDGE-BRIDGE-AND-Q-CLASSES.md Part 2:
       (A) all C(6)=132 triangulations of the 8-gon (ring labels 0,2,...,8): none has all faces
           consecutive in C_9;
       (B) edge-disjoint ear sets on the 9-cycle = independent sets of C_9: sizes 1+9+27+30+9,
           none of size 5  =>  q <= 4.
"""
import json
import math
from itertools import combinations
from pathlib import Path

HERE = Path(__file__).parent


# ---------------- (1) MEC vs circumradius for equal disks ----------------
def disk_triple_counterexample():
    r = 1.0
    u, v, w = (-0.9, 0.0), (0.9, 0.0), (0.0, 0.1)
    # common point (0,0)?
    common = (0.0, 0.0)
    in_all = all(math.hypot(common[0] - c[0], common[1] - c[1]) <= r + 1e-15 for c in (u, v, w))
    # MEC radius (obtuse at w: longest side = |u-v| = 1.8 < 2)
    mec = max(math.hypot(u[0] - v[0], u[1] - v[1]),
              math.hypot(u[0] - w[0], u[1] - w[1]),
              math.hypot(v[0] - w[0], v[1] - w[1])) / 2.0
    # circumradius
    def d2(a, b):
        return (a[0] - b[0]) ** 2 + (a[1] - b[1]) ** 2
    a2, b2, c2 = d2(v, w), d2(w, u), d2(u, v)
    cross = (v[0] - u[0]) * (w[1] - u[1]) - (v[1] - u[1]) * (w[0] - u[0])
    circ = math.sqrt(a2 * b2 * c2) / (2 * abs(cross))
    return {'centers': [u, v, w], 'r': r, 'common_point': common, 'common_point_covered': in_all,
            'MEC': mec, 'MEC_le_r': mec <= r, 'circumradius': circ, 'circumradius_le_r': circ <= r,
            'conclusion': 'shared point holds (MEC<=r) while circumradius>r -> Rc<=r clause false'}


# ---------------- (2A) 8-gon triangulations, no all-consecutive ----------------
def consecutive_triple(labels):
    s = set(labels)
    return any(s == {(j % 9), ((j + 1) % 9), ((j + 2) % 9)} for j in range(9))


def triangulations(poly):
    """all triangulations of a convex polygon given as a cyclic list of labels (DP, returns list)."""
    if len(poly) < 3:
        return [[]]
    if len(poly) == 3:
        return [[tuple(poly)]]
    out = []
    a, b = poly[0], poly[-1]
    for k in range(1, len(poly) - 1):
        mid = poly[k]
        for left in triangulations(poly[:k + 1]):
            for right in triangulations(poly[k:]):
                out.append([(a, mid, b)] + left + right)
    return out


def check_8gon():
    poly = [0, 2, 3, 4, 5, 6, 7, 8]
    tris = triangulations(poly)
    all_cons = [t for t in tris if all(consecutive_triple(f) for f in t)]
    return {'n_triangulations': len(tris), 'n_all_consecutive': len(all_cons),
            'matches_132': len(tris) == 132, 'none_all_consecutive': len(all_cons) == 0}


# ---------------- (2B) independent sets of C_9 ----------------
def check_ears():
    counts = {}
    for size in range(0, 6):
        c = 0
        for S in combinations(range(9), size):
            if all((S[i + 1] - S[i]) > 1 and not (S[0] + 9 - S[-1] == 1) for i in range(len(S) - 1)) \
                    and not (len(S) == 9):
                if len(S) == 0 or (S[0] + 9 - S[-1] != 1):
                    c += 1
        counts[size] = c
    return {'independent_set_counts_sizes_0_to_5': counts,
            'matches_1_9_27_30_9': [counts[i] for i in range(5)] == [1, 9, 27, 30, 9],
            'none_of_size_5': counts[5] == 0}


def main():
    out = {'role': 'independent graph-interface verification (no claim registered)'}
    out['counterexample'] = disk_triple_counterexample()
    out['eight_gon'] = check_8gon()
    out['ears'] = check_ears()
    print('(1) obtuse triple: common point covered = %s, MEC = %.4f <= r = %s, circumradius = %.4f <= r = %s'
          % (out['counterexample']['common_point_covered'], out['counterexample']['MEC'],
             out['counterexample']['MEC_le_r'], out['counterexample']['circumradius'],
             out['counterexample']['circumradius_le_r']))
    print('(2A) 8-gon: %d triangulations (==132: %s), all-consecutive: %d (none: %s)'
          % (out['eight_gon']['n_triangulations'], out['eight_gon']['matches_132'],
             out['eight_gon']['n_all_consecutive'], out['eight_gon']['none_all_consecutive']))
    print('(2B) ear sets: %s (matches 1+9+27+30+9: %s; none of size 5: %s)'
          % (out['ears']['independent_set_counts_sizes_0_to_5'],
             out['ears']['matches_1_9_27_30_9'], out['ears']['none_of_size_5']))
    (HERE / 'graph_interface_check.json').write_text(json.dumps(out, indent=2))
    print('saved graph_interface_check.json')


if __name__ == '__main__':
    main()
