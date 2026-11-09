"""Certify strict local optimality for the unrestricted centers modulo rotation."""

from fractions import Fraction as Q

from refine_template import dot, ring, sub, template
from verify_template import Interval as I, Jet, cross, require, root_box


COORDS = 53
GAUGE = [j for j in range(COORDS) if j != 1]
TRIANGLES_Q1 = ((1, 2, 17), (3, 4, 18), (1, 17, 16), (3, 18, 17), (17, 18, 24))


def norm2(a):
    return a[0]**2 + a[1]**2


def rot(a):
    return -a[1], a[0]


def circumcenter(p, q, s):
    a, b = sub(q, p), sub(s, p)
    det = cross(a, b)
    j, k = rot(a), rot(b)
    return tuple(p[i] + (norm2(b) * j[i] - norm2(a) * k[i]) / (2 * det) for i in (0, 1))


def transform(i, sx, sy):
    sign = sx * sy
    if i < 16:
        return ((0 if sx > 0 else 8) + sign * i) % 16
    if i < 24:
        return 16 + ((0 if sx > 0 else 4) + sign * (i - 16)) % 8
    return i if sx > 0 else 49 - i


def positive_triangles():
    for sx, sy in ((1, 1), (-1, 1), (-1, -1), (1, -1)):
        for tri in TRIANGLES_Q1:
            yield tuple(transform(i, sx, sy) for i in tri)


def variables(sites, q, ids):
    columns = [2*i+j for i in ids for j in (0, 1)] + [52]
    values = [sites[i][j] for i in ids for j in (0, 1)] + [q]
    z = [Jet.variable(x, j, len(columns)) for j, x in enumerate(values)]
    return columns, list(zip(z[::2], z[1::2])), z[-1]


def circle_endpoint(p, q, sign):
    p2 = norm2(p)
    t = p2.sqrt()
    c = (1 + p2 - q) / (2 * t)
    s = (1 - c**2).sqrt()
    return tuple((c * a + sign * s * b) / t for a, b in zip(p, rot(p)))


def verify_witness(p, sites, q, ids):
    require(all((norm2(sub(p, s)) - q).lo > 0 for j, s in enumerate(sites) if j not in ids),
            f"Noncontacting site cannot be separated at {ids}")


def constraints(sites, q, seams=None):
    for ids in positive_triangles():
        witness = circumcenter(*(sites[i] for i in ids))
        require(norm2(witness).hi < I(1).lo, "Circumcenter outside the unit disk")
        verify_witness(witness, sites, q, ids)
        columns, (a, b, c), r2 = variables(sites, q, ids)
        x, y, z = sub(b, a), sub(c, a), sub(c, b)
        radius2 = norm2(x) * norm2(y) * norm2(z) / (4 * cross(x, y)**2)
        yield columns, radius2 - r2
    for i in range(16):
        ids = i, (i+1) % 16
        if seams is not None:
            seam = seams[i]
            verify_witness(seam, sites, q, ids)
            require(cross(sites[ids[0]], seam).lo > 0 and cross(sites[ids[1]], seam).hi < 0,
                    "Seam is not the correct endpoint of both arcs")
        else:
            right = circle_endpoint(sites[ids[0]], q, 1)
            left = circle_endpoint(sites[ids[1]], q, -1)
            require(dot(right, left).lo > 0, "Arc endpoints too far apart")
            verify_witness(right, sites, q, ids)
        columns, (a, b), r2 = variables(sites, q, ids)
        yield columns, cross(circle_endpoint(a, r2, 1), circle_endpoint(b, r2, -1))


def reduced_rows(rows):
    """Row reduce with a verified nonsingular pivot block."""
    a = [row.copy() for row in rows]
    n, m = len(a), len(a[0])
    columns = list(range(m))
    for i in range(n):
        r, s = max(((j, k) for j in range(i, n) for k in range(i, m)),
                   key=lambda jk: abs(a[jk[0]][jk[1]].lo + a[jk[0]][jk[1]].hi))
        a[i], a[r] = a[r], a[i]
        columns[i], columns[s] = columns[s], columns[i]
        for row in a:
            row[i], row[s] = row[s], row[i]
        pivot = a[i][i].reciprocal()
        a[i][i] = I(1)
        for k in range(i+1, m):
            a[i][k] *= pivot
        for j in range(n):
            if j != i:
                factor = a[j][i]
                a[j][i] = I(0)
                for k in range(i+1, m):
                    a[j][k] -= factor * a[i][k]
    return columns, a


def solve_square(a, rhs):
    n = len(rhs)
    a = [list(row) + [b] for row, b in zip(a, rhs)]
    for i in range(n):
        j = max(range(i, n), key=lambda j: abs(a[j][i].lo + a[j][i].hi))
        a[i], a[j] = a[j], a[i]
        pivot = a[i][i].reciprocal()
        for k in range(i+1, n+1):
            a[i][k] *= pivot
        for j in range(n):
            if j != i:
                factor = a[j][i]
                for k in range(i+1, n+1):
                    a[j][k] -= factor * a[i][k]
    return [row[-1] for row in a]


def pd_check(a, factor=False):
    """Interval Schur complements certify positive definiteness."""
    n = len(a)
    minimum = a[0][0].lo
    lower = [[I(i == j) for j in range(n)] for i in range(n)] if factor else None
    for i in range(n):
        require(a[i][i].lo > 0, f"Nonpositive LDL pivot {i}")
        minimum = min(minimum, a[i][i].lo)
        inv = a[i][i].reciprocal()
        for j in range(i+1, n):
            coeff = a[j][i] * inv
            if lower is not None:
                lower[j][i] = I(coeff.midpoint())
            for k in range(j, n):
                a[k][j] -= coeff * a[k][i]
                a[j][k] = a[k][j]
    return (minimum, lower) if factor else minimum


def matmul(a, b):
    cols = list(zip(*b))
    return [[sum(x*y for x, y in zip(row, col)) for col in cols] for row in a]


def hessian(derivatives, multipliers, penalty=0):
    h = [[I(0)] * COORDS for _ in range(COORDS)]
    for mu, (js, fun) in zip(multipliers, derivatives):
        factor = mu + penalty * fun.v
        for a, j in enumerate(js):
            for b, k in enumerate(js):
                h[j][k] += factor * fun.h[a][b] + penalty * fun.g[a] * fun.g[b]
    return h


def inverse_lower(lower):
    n = len(lower)
    inv = [[I(i == j) for j in range(n)] for i in range(n)]
    for i in range(n):
        for j in range(i):
            inv[i][j] = I((-sum(lower[i][k] * inv[k][j] for k in range(j, i))).midpoint())
    return inv


def verify_neighborhood(sites, r2, multipliers, columns, base_derivatives, width=Q("1e-9"), penalty=100):
    enlarge = I(-width, width)
    expanded = [tuple(v + enlarge if (i, j) != (0, 1) else v for j, v in enumerate(p))
                for i, p in enumerate(sites)]
    ders = list(constraints(expanded, r2 + enlarge))
    require(all(penalty * f.v.magnitude() < 2 * Q(mu.lo, I(1).lo)
                for mu, (_, f) in zip(multipliers, ders)), "Penalty term too large on the box")
    base = hessian(base_derivatives, multipliers, penalty)
    _, lower = pd_check([[base[j][k] for k in columns] for j in columns], factor=True)
    precondition = inverse_lower(lower)
    h = hessian(ders, multipliers, penalty)
    h = [[h[j][k] for k in columns] for j in columns]
    transformed = matmul(matmul(precondition, h), list(zip(*precondition)))
    require(all(Q(row[i].lo, I(1).lo) > sum(v.magnitude() for j, v in enumerate(row) if i != j)
                for i, row in enumerate(transformed)), "Augmented Hessian is not verified on the box")
    print(f"PASS: explicit local box of coordinate half-width {float(width):g} (including q = r^2)")


def template_configuration():
    _, _, box = root_box()
    _, outer, middle, core, seams_q1 = template(*box, with_seams=True)
    r2 = box[0]**2
    sites = ring(outer) + ring(middle) + [core, (-core[0], core[1])]
    seams = []
    for sx, sy in ((1, 1), (-1, 1), (-1, -1), (1, -1)):
        seq = seams_q1 if sx * sy > 0 else seams_q1[::-1]
        seams.extend((sx * x, sy * y) for x, y in seq)
    return sites, seams, r2


def stationary_multipliers(sites, seams, r2):
    derivatives = list(constraints(sites, r2, seams))
    rows = []
    for columns, fun in derivatives:
        row = [I(0)] * COORDS
        for c, g in zip(columns, fun.g):
            row[c] = g
        rows.append([row[j] for j in GAUGE])
    order, reduced = reduced_rows(rows)
    n, m = len(rows), len(GAUGE)
    columns = [GAUGE[i] for i in order]
    pivot_transpose = [[row[j] for row in rows] for j in order[:n]]
    multipliers = solve_square(pivot_transpose, [I(-int(j == 52)) for j in columns[:n]])
    require(all(x.lo > 0 for x in multipliers), "A multiplier is not strictly positive")
    return derivatives, reduced, columns, multipliers


def main():
    sites, seams, r2 = template_configuration()
    derivatives, reduced, columns, multipliers = stationary_multipliers(sites, seams, r2)
    n, m = len(reduced), len(columns)

    # Stationarity in all coordinates follows from the reflection argument
    # in proof.md. Here the pivot block encloses its unique multipliers.
    h = hessian(derivatives, multipliers)
    h = [[h[j][k] for k in columns] for j in columns]
    basis = [[-reduced[i][j] for j in range(n, m)] for i in range(n)]
    basis.extend([I(i == j) for j in range(m-n)] for i in range(m-n))
    restricted = matmul(list(zip(*basis)), matmul(h, basis))
    min_pivot = Q(pd_check(restricted), I(1).lo)
    require(min_pivot > Q(".037"), "Unexpectedly small tangent pivot")
    print(f"PASS: {n} locally necessary contacts, full row rank, all multipliers positive")
    print(f"PASS: positive Hessian on the {m-n}-dimensional tangent, min LDL pivot > 0.037")
    verify_neighborhood(sites, r2, multipliers, columns, derivatives)


if __name__ == "__main__":
    main()
