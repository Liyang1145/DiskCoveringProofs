"""Root-box transport certifying n22 candidate D7 symmetry and scalar cubic.

The mathematical transport/branch argument is in N22-RADIUS-LINK.md.
Floating distances only propose an internal-label permutation; all accepted
maps and every inclusion in the unique outer root box are checked exactly.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse
import json
import math
from stream_catalog import sha

ROOT = Path(__file__).resolve().parent
assert __debug__


def add(a, b):
    return a[0]+b[0], a[1]+b[1]


def neg(a):
    return -a[1], -a[0]


def sub(a, b):
    return add(a, neg(b))


def mul(a, b):
    values = [x*y for x in a for y in b]
    return min(values), max(values)


def norm2(p):
    return add(mul(p[0], p[0]), mul(p[1], p[1]))


def dot(p, q):
    return add(mul(p[0], q[0]), mul(p[1], q[1]))


def compose(p, q):
    return [p[q[i]] for i in range(len(p))]


def orbit(p, i):
    out, current = [], i
    while current not in out:
        out.append(current)
        current = p[current]
    assert current == i
    return out


def pmul(a, b):
    result = [0]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            result[i+j] += x*y
    return result


def padd(*polynomials):
    result = [sum(p[i] if i < len(p) else 0 for p in polynomials)
              for i in range(max(map(len, polynomials)))]
    while len(result) > 1 and result[-1] == 0:
        result.pop()
    return result


def peval(coefficients, value):
    result = F(0)
    for coefficient in reversed(coefficients):
        result = result*value+coefficient
    return result


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    folder = ROOT.parent / "evidence/n22"
    rootpath, systempath = folder / "core-root.json", folder / "core-system.json"
    root, data = (json.loads(p.read_text()) for p in (rootpath, systempath))
    paid = json.loads((folder / "algebraic-check1/root-verified.json").read_text())
    assert paid["verified"] and paid["root_sha256"] == sha(rootpath)
    assert paid["system_sha256"] == sha(systempath)
    assert {F(box["rho"]) for box in paid["boxes"]} == {F(1, 10**60), F(1, 10**80)}
    # The root acceptor records inclusion divided by box half-width.
    assert all(F(box["inclusion"]) < 1 and F(box["contraction"]) < 1
               for box in paid["boxes"])
    B, N, G, M = 14, 22, 126, 112
    assert (data["B"], data["N"], data["G"], data["D"]) == (B, N, G, 252)
    assert len(data["edges"]) == M and data["center_core_nodes"] == list(range(B, B+N))
    faces = [tuple(face) for face in data["active_faces"]]
    assert len(faces) == 28 and sorted(faces) == sorted(map(tuple, data["all_faces"]))
    midpoint = [F(int(value), int(root["Qx"])) for value in root["xnum"]]
    assert len(midpoint) == 252
    small, outer = F(1, 10**80), F(1, 10**60)
    intervals = [(value-small, value+small) for value in midpoint]
    points = [[(F(1), F(1)), (F(0), F(0))]] + [intervals[2*i:2*i+2] for i in range(G//2)]
    centre_mid = [[float(midpoint[2*(B+j-1)+axis]) for axis in (0, 1)] for j in range(N)]
    weights = intervals[G+1:G+1+M]
    fullmu = [None]+intervals[G+1+M:]
    reaction = (F(0), F(0))
    for edge, weight in zip(data["edges"], weights):
        if 0 in edge:
            other = edge[1] if edge[0] == 0 else edge[0]
            reaction = add(reaction, mul(weight, sub((F(1), F(1)), points[other][0])))
    fullmu[0] = neg(reaction)
    faceindex = {tuple(sorted(face)): j for j, face in enumerate(faces)}
    edgeindex = {frozenset(edge): j for j, edge in enumerate(data["edges"])}
    assert len(edgeindex) == M
    records = []
    centre_maps = []
    for sign, anchor_shift in ((1, 2), (-1, 1)):
        cx = float(midpoint[2*(anchor_shift-1)])
        cy = float(midpoint[2*(anchor_shift-1)+1])
        def propose(point):
            x, y = point
            return [cx*x-cy*y, cy*x+cx*y] if sign == 1 else [cx*x+cy*y, cy*x-cx*y]
        centre = ([(i+2) % B for i in range(B)] if sign == 1 else [(2-i) % B for i in range(B)])
        for i in range(B, N):
            transformed = propose(centre_mid[i])
            chosen = min(range(B, N), key=lambda j: sum((centre_mid[j][axis]-transformed[axis])**2 for axis in (0, 1)))
            centre.append(chosen)
        assert sorted(centre) == list(range(N))
        anchor = [(i+2) % B for i in range(B)] if sign == 1 else [(1-i) % B for i in range(B)]
        mappedfaces = [faceindex[tuple(sorted(centre[v] for v in face))] for face in faces]
        pointmap = anchor+[B+v for v in centre]+[B+N+j for j in mappedfaces]
        assert sorted(pointmap) == list(range(64))
        mappededges = [edgeindex[frozenset(pointmap[v] for v in edge)] for edge in data["edges"]]
        assert sorted(mappededges) == list(range(M))
        for i in range(B):
            assert {centre[i], centre[(i+1) % B]} == {anchor[i], (anchor[i]+1) % B}
        qx, qy = points[anchor[0]]
        new = []
        for node in range(1, 64):
            zx, zy = points[pointmap[node]]
            x = add(mul(qx, zx), mul(qy, zy))
            y = sub(mul(qx, zy), mul(qy, zx))
            new.extend((x, y if sign == 1 else neg(y)))
        new.append(intervals[G])
        new.extend(weights[j] for j in mappededges)
        new.extend(fullmu[anchor[i]] for i in range(1, B))
        assert len(new) == 252
        margins = [min(lo-(value-outer), (value+outer)-hi) for (lo, hi), value in zip(new, midpoint)]
        assert min(margins) > 0, ("symmetry root transport not inside unique outer box", sign)
        records.append({"orientation": sign, "point_permutation": pointmap,
                        "edge_permutation": mappededges, "centre_permutation": centre,
                        "outer_box_strict_inclusion_margin": str(min(margins))})
        centre_maps.append(centre)
    rotation, reflection = centre_maps
    assert all(len(orbit(rotation, i)) in (1, 7) for i in range(N))
    assert compose(reflection, reflection) == list(range(N))
    assert compose(reflection, compose(rotation, reflection)) == [orbit(rotation, i)[-1] for i in range(N)]
    central = [i for i in range(B, N) if rotation[i] == i]
    inner = [i for i in range(B, N) if reflection[i] == i and len(orbit(rotation, i)) == 7]
    assert len(central) == len(inner) == 1
    origin, first = central[0], inner[0]
    next_inner = rotation[first]
    assert {tuple(sorted(face)) for face in ((origin, first, next_inner), (first, 2, next_inner), (first, 1, 2))} <= set(faceindex)
    assert rotation[reflection[2]] == 2
    c = points[2][0]
    assert F(62, 100) < c[0] <= c[1] < F(63, 100)
    assert points[2][1][0] > 0
    t = intervals[G]
    a2, b2, d2 = (norm2(points[B+i]) for i in (first, 1, 2))
    assert dot(points[B+first], points[B+1])[0] > 0
    assert dot(points[B+2], [add(points[B+first][axis], points[B+next_inner][axis]) for axis in (0, 1)])[0] > 0
    assert a2[0] > 0 and b2[0] > a2[1]
    assert d2[0] > 4*t[1] and b2[0] > 4*a2[1]*c[1]**2
    assert (5+4*c[1])*t[1] < 1
    assert F(641, 10000) < t[0] <= t[1] < F(642, 10000)
    # Integer identities used by the written scalar elimination.
    P, D, E = [-1, -4, 4, 8], [5, 12, 8], [5, 4]
    assert pmul(D, E) == [25, 80, 88, 32]
    # Elimination of the two unit-anchor distance equations:
    # (1+c)(1+(7+8c)t)^2+(1-c)(1-t)^2-32(1+c)^2t
    # = 2(Dt-1)(Et-1). Check all three t-coefficients.
    assert padd([1, 1], [1, -1]) == [2]
    assert padd([2*v for v in pmul([1, 1], [7, 8])], [-2, 2],
                [-32, -64, -32]) == [-2*v for v in padd(D, E)]
    assert padd(pmul([1, 1], pmul([7, 8], [7, 8])),
                [1, -1]) == [2*v for v in pmul(D, E)]
    D2, D3 = pmul(D, D), pmul(pmul(D, D), D)
    numerator = [(29 if i == 0 else 0) - (55*D[i] if i < len(D) else 0) +
                 (19*D2[i] if i < len(D2) else 0) - D3[i] for i in range(7)]
    assert numerator == pmul(P, [-104, -304, -256, -64])
    Tlo, Thi = F(641, 10000), F(642, 10000)
    scalar = [-1, 19, -55, 29]
    assert peval(scalar, Tlo) < 0 < peval(scalar, Thi)
    assert 87*Tlo*Tlo-110*Thi+19 > 0
    report = {"verified": True, "N": 22, "root_sha256": sha(rootpath), "system_sha256": sha(systempath),
              "paid_unique_root_report_sha256": sha(folder / "algebraic-check1/root-verified.json"),
              "symmetry_transports": records, "central_centre": origin, "inner_axis_centre": first,
              "branch_guards": {"short_greater_than_twice_r": True, "long_wrong_branch_excluded": True,
                                "radius_wrong_branch_excluded": True},
              "linked_radius_square_polynomial_ascending": scalar,
              "unit_anchor_elimination_identity_integer_checked": True,
              "radius_square_isolating_interval": [str(Tlo), str(Thi)],
              "candidate_symmetry_D7_certified": True,
              "arbitrary_optimal_cover_symmetry_assumed": False,
              "global_optimality_proved": False, "source_sha256": sha(Path(__file__))}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2), encoding="utf8")
    print("N22 EXACT unique-root D7 transport and radius cubic link PASS", flush=True)


if __name__ == "__main__":
    main()
