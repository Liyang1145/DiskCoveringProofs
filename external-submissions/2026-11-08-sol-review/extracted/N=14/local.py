"""Certify strict local optimality of the exact construction modulo rotations."""

from itertools import product

from interval import Interval as I, SCALE
from upper import ROOT_R, ROOT_T, geometry


def dot(a, b):
    return sum(x*y for x, y in zip(a, b))


def subtract(a, b):
    return tuple(x-y for x, y in zip(a, b))


def cross(a, b):
    return a[0]*b[1]-a[1]*b[0]


def quarter_turn(p):
    return -p[1], p[0]


def reflect(p, sx, sy):
    return sx*p[0], sy*p[1]


def sign_margin(x):
    return max(x.lo, -x.hi)


def row_reduce(rows, columns):
    """Reduce an exact matrix enclosed by rows, with column permutations."""
    a = [row[:] for row in rows]
    permutation = list(range(columns))
    for k in range(len(a)):
        _, i, j = max((sign_margin(a[i][j]), i, j)
                      for i in range(k, len(a)) for j in range(k, columns))
        assert sign_margin(a[i][j]) > 0, (i, j)
        a[k], a[i] = a[i], a[k]
        for row in a:
            row[k], row[j] = row[j], row[k]
        permutation[k], permutation[j] = permutation[j], permutation[k]
        divisor = a[k][k]
        a[k] = [value/divisor for value in a[k]]
        a[k][k] = I(1)
        for i, row in enumerate(a):
            if i != k:
                multiple = row[k]
                a[i] = [value-multiple*pivot for value, pivot in zip(row, a[k])]
                a[i][k] = I(0)
    return a, permutation


def kernel(rows):
    count = len(rows[0])
    reduced, perm = row_reduce(rows, count)
    basis = []
    for free in range(len(rows), count):
        v = [I(0)]*count
        v[perm[free]] = I(1)
        for i, row in enumerate(reduced):
            v[perm[i]] = -row[free]
        basis.append(v)
    return basis


def weights_at(x, centers):
    a, b, *remaining = centers
    if not remaining:
        c0, c1 = cross(a, x), cross(b, x)
        t = -c1/(c0-c1)
        return t, 1-t
    c = remaining[0]
    p, q, z = subtract(b, a), subtract(c, a), subtract(x, a)
    area = cross(p, q)
    s, t = cross(z, q)/area, cross(p, z)/area
    return 1-s-t, s, t


def contact_data(r, coords):
    signs = list(product((1, -1), repeat=2))

    def key(label, sx, sy):
        if label == "A":
            sy = 1
        if label in "BE":
            sx = 1
        return label, sx, sy

    labels = list(dict.fromkeys(key(label, sx, sy) for label in "ABEPQ" for sx, sy in signs))
    centers = [reflect(coords[label], sx, sy) for label, sx, sy in labels]
    assert len(centers) == 14
    neighbors = {
        "X": [("P", 1, 1), ("P", 1, -1)],
        "S": [("P", 1, 1), ("Q", 1, 1)],
        "T": [("E", 1, 1), ("Q", 1, 1)],
        "U": [("A", 1, 1), ("P", 1, 1), ("Q", 1, 1)],
        "W": [("A", 1, 1), ("B", 1, 1), ("Q", 1, 1)],
    }
    contacts = []
    for group, adjacent in neighbors.items():
        for sx, sy in signs:
            if group == "X" and sy == -1:
                continue
            x = reflect(coords[group], sx, sy)
            indices = [labels.index(key(label, ux*sx, uy*sy)) for label, ux, uy in adjacent]
            if len(indices) == 3:
                assert dot(x, x).hi < I(1).lo
            offsets = [subtract(p, x) for p in centers]
            for i, offset in enumerate(offsets):
                if i not in indices:
                    assert (dot(offset, offset)-r.square()).lo > 0, (group, sx, sy, labels[i])
            lam = weights_at(x, [centers[i] for i in indices])
            assert all(w.lo > 0 for w in lam)
            gradient = [I(0)]*28
            for i, w in zip(indices, lam):
                gradient[2*i:2*i+2] = [2*w*y for y in offsets[i]]
            contacts.append((group, x, indices, lam, gradient))
    assert len(contacts) == 18
    return labels, centers, contacts


def stationary_weights(labels, contacts):
    groups = "XSTUW"
    gradients = {g: [sum(data[-1][k] for data in contacts if data[0] == g)
                     for k in range(28)] for g in groups}
    coordinates = [2*labels.index((p, 1, 1))+axis for p in "PQ" for axis in range(2)]
    system = [[gradients[g][j] for g in groups[1:]]+[-gradients["X"][j]]
              for j in coordinates]
    reduced, perm = row_reduce(system, 4)
    weights = {"X": I(1)}
    for i, row in enumerate(reduced):
        weights[groups[1+perm[i]]] = row[-1]
    assert all(w.lo > 0 for w in weights.values()), weights
    return weights


def witness_velocity(x, points, velocities):
    a, b, *remaining = points
    p = subtract(b, a)
    rhs = dot(subtract(x, a), velocities[0])-dot(subtract(x, b), velocities[1])
    if not remaining:
        tangent = quarter_turn(x)
        factor = rhs/dot(p, tangent)
        return tuple(factor*y for y in tangent)
    c = remaining[0]
    q = subtract(c, a)
    rhs2 = dot(subtract(x, a), velocities[0])-dot(subtract(x, c), velocities[2])
    determinant = cross(p, q)
    return ((rhs*q[1]-p[1]*rhs2)/determinant,
            (p[0]*rhs2-rhs*q[0])/determinant)


def projected_hessian(centers, contacts, weights, basis):
    size = len(basis)
    h = [[I(0) for _ in basis] for _ in basis]
    for group, x, indices, lam, _ in contacts:
        points = [centers[i] for i in indices]
        velocities = [[v[2*i:2*i+2] for i in indices] for v in basis]
        shifts = [witness_velocity(x, points, v) for v in velocities]
        relative = [[subtract(y, v) for v in vv] for y, vv in zip(shifts, velocities)]
        mu = 1-sum(w*dot(x, p) for w, p in zip(lam, points)) if len(indices) == 2 else I(0)
        for i in range(size):
            for j in range(i, size):
                value = sum(w*dot(a, b) for w, a, b in zip(lam, relative[i], relative[j]))
                h[i][j] += 2*weights[group]*(value-mu*dot(shifts[i], shifts[j]))
    return h


def positive_pivots(upper):
    pivots = []
    for i, row in enumerate(upper):
        pivot = row[i]
        assert pivot.lo > 0, (i, pivot)
        pivots.append(pivot)
        for j in range(i+1, len(upper)):
            for k in range(j, len(upper)):
                upper[j][k] -= row[j]*row[k]/pivot
    return pivots


def main():
    r, t = ROOT_R, ROOT_T
    _, coords = geometry(r, t)
    coords = {k: tuple(map(I.coerce, p)) for k, p in coords.items()}
    labels, centers, contacts = contact_data(r, coords)
    weights = stationary_weights(labels, contacts)
    fixed = 2*labels.index(("A", 1, 1))+1
    # Drop the first X row using the positive stationary dependence.
    rows = [row[:fixed]+row[fixed+1:] for _, _, _, _, row in contacts[1:]]
    reduced = kernel(rows)
    basis = [v[:fixed]+[I(0)]+v[fixed:] for v in reduced]
    assert len(basis) == 10
    pivots = positive_pivots(projected_hessian(centers, contacts, weights, basis))
    print("18 active witnesses, 17 independent gradients after fixing orientation.")
    print("Positive stationary weights (X, S, T, U, W):")
    print(" ".join(f"{weights[g].lo / SCALE:.8f}" for g in "XSTUW"))
    print("Certified positive Hessian pivots:")
    print(" ".join(f"{p.lo / SCALE:.8f}" for p in pivots))


if __name__ == "__main__":
    main()
