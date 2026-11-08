"""Exact exclusion below R when the reference mesh cuts are sufficiently close."""

from functools import lru_cache
from itertools import permutations

from interval import Interval as I, PI
from local import contact_data, dot, positive_pivots, quarter_turn, stationary_weights
from upper import ROOT_R, ROOT_T, geometry


KAPPA = I(".07")
GAMMA = I("9.36")
SIGMA = I("6.27")


@lru_cache(maxsize=1)
def reference():
    _, coords = geometry(ROOT_R, ROOT_T)
    coords = {k: tuple(map(I.coerce, p)) for k, p in coords.items()}
    labels, centers, contacts = contact_data(ROOT_R, coords)
    names = [
        ("P", 1, -1), ("P", 1, 1), ("Q", 1, 1), ("E", 1, 1), ("Q", -1, 1),
        ("P", -1, 1), ("P", -1, -1), ("Q", -1, -1), ("E", 1, -1), ("Q", 1, -1),
        ("A", 1, 1), ("B", 1, 1), ("A", -1, 1), ("B", 1, -1),
    ]
    index = {label: names.index(label) for label in labels}
    faces = [tuple(index[labels[i]] for i in ids) for _, _, ids, _, _ in contacts if len(ids) == 3]
    for sx in (1, -1):
        a = index["A", sx, 1]
        faces.append((a, index["B", 1, 1], index["B", 1, -1]))
        faces.append((a, index["P", sx, 1], index["P", sx, -1]))
        for sy in (1, -1):
            faces.append((index["Q", sx, sy], index["E", 1, sy], index["B", 1, sy]))
    cut_points = {}
    for _, x, ids, _, _ in contacts:
        if len(ids) == 2:
            cut_points[frozenset(index[labels[i]] for i in ids)] = x
    cuts = [cut_points[frozenset((j, (j+1) % 10))] for j in range(10)]
    return tuple(sorted(tuple(sorted(f)) for f in faces)), cuts, labels, centers, contacts


def verified_pivots():
    _, _, labels, centers, contacts = reference()
    weights = stationary_weights(labels, contacts)
    fixed = 14
    assert contacts[0][0] == "X" and contacts[0][1][0].lo == I(1).lo
    assert contacts[0][1][1].lo == contacts[0][1][1].hi == 0
    size = 2*(14+len(contacts)-1)
    matrix = [[I(0) for _ in range(size)] for _ in range(size)]
    weighted_radials = []

    def col(v, k):
        return 2*(v-int(v > fixed))+k

    def add_square(coefficients, weight):
        coefficients = sorted(coefficients)
        for t, (i, a) in enumerate(coefficients):
            for j, b in coefficients[t:]:
                matrix[i][j] += weight*a*b

    for j, (g, x, indices, lambdas, _) in enumerate(contacts, 14):
        a = [weights[g]*w for w in lambdas]
        for i, w in zip(indices, a):
            term = []
            for k in range(2):
                columns = [(col(i, k), 1)]
                if j != fixed:
                    columns.append((col(j, k), -1))
                add_square(columns, w)
                delta = w*(centers[i][k]-x[k])
                term.extend((c, sign*delta) for c, sign in columns)
            add_square(term, GAMMA)
        if len(indices) == 2 and j != fixed:
            mu = sum(w*(1-dot(x, centers[i])) for i, w in zip(indices, a))
            for k in range(2):
                matrix[col(j, k)][col(j, k)] -= mu
            radial = [(col(j, k), x[k]) for k in range(2)]
            tangent = [(col(j, k), u) for k, u in enumerate(quarter_turn(x))]
            weighted_radials.extend((c, mu*u) for c, u in radial)
            add_square(radial, SIGMA)
            add_square(tangent, -SIGMA*KAPPA.square())
    add_square(weighted_radials, -GAMMA)
    return positive_pivots(matrix)


@lru_cache(maxsize=1)
def verify_neighborhood():
    pivots = verified_pivots()
    return len(pivots), min(p.lo for p in pivots)


def reference_matching(faces):
    own_faces, _, _, _, _ = reference()
    for sign in (1, -1):
        for offset in range(10):
            outer = tuple((sign*j+offset) % 10 for j in range(10))
            for inner in permutations(range(10, 14)):
                perm = outer+inner
                test = tuple(sorted(tuple(sorted(perm[i] for i in f)) for f in own_faces))
                if test == faces:
                    yield sign, tuple(outer[(j+int(sign < 0)) % 10] for j in range(10))


def near_checker(n, faces, r):
    if n != 10:
        return None
    matches = list(reference_matching(faces))
    if not matches:
        return None
    from network import angle_box, unit_at

    verify_neighborhood()
    _, cuts, _, _, _ = reference()
    cosine = (1-KAPPA.square())/(1+KAPPA.square())

    def check(box):
        angle = angle_box(10, r, box)
        for sign, match in matches:
            anchor_lo, anchor_hi = angle[match[0]]
            for j in range(1, 10):
                a, b = angle[match[j]]
                low, high = a-anchor_hi, b-anchor_lo
                if sign < 0:
                    low, high = -high, -low
                if high.hi-low.lo >= PI.lo:
                    break
                lower = min(dot(cuts[j], unit_at(x.lo, x.hi)).lo for x in (low, high))
                if lower <= cosine.hi:
                    break
            else:
                return True
        return False

    return check


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Run the certificate with assertions enabled.")
    from interval import SCALE

    count, least = verify_neighborhood()
    print("Verified", count, "positive pivots, smallest lower endpoint", least/SCALE)
