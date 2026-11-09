"""Certify the lower bound for the incidence graph in topology.md."""

from fractions import Fraction as Q

from verify import PI, Interval, asin, cos, interval, sin, sqrt, square


def rounded(x, scale=10**32):
    lo = (x.lo * scale).__floor__()
    hi = (x.hi * scale).__ceil__()
    return Interval(Q(lo, scale), Q(hi, scale))


def graph(k):
    """Witness nodes 0:14 and 36:64, site nodes 14:36."""
    w_a = interval(1)
    w_b = 2*(k-1)/k
    m = k-3
    b = w_b-m
    a = b*(k-3) + m*(k-2)
    edges = []
    for i in range(7):
        j = (i+1) % 7
        i0, i1 = 14+i, 14+j
        a0, a1, b0, origin = 21+i, 21+j, 28+i, 35
        u, v, w0, w1 = 36+i, 43+i, 50+i, 57+i
        z0, z1 = 2*i+1, 2*j
        for witness, neighbors in (
            (z0, ((a0, w_a), (b0, w_b))),
            (z1, ((a1, w_a), (b0, w_b))),
            (u, ((origin, a*(k-2)), (i0, a), (i1, a))),
            (v, ((b0, b*(k-2)), (i0, b), (i1, b))),
            (w0, ((i0, m*(k-2)), (a0, m), (b0, m))),
            (w1, ((i1, m*(k-2)), (a1, m), (b0, m))),
        ):
            edges.extend((witness, site, weight) for site, weight in neighbors)
    return edges


def check_incidences(c, s, k, edges):
    """Check that the intended witnesses see precisely their incident sites."""
    def rotate(p, rot):
        x, y = p
        u, v = rot
        return rounded(x*u-y*v), rounded(x*v+y*u)

    step = (2*square(c)-1, 2*c*s)
    rot = (interval(1), interval(0))
    sites = {35: (interval(0), interval(0))}
    witnesses = {}
    for i in range(7):
        sites[14+i] = rotate((2*c, interval(0)), rot)
        sites[21+i] = rotate((4*c, interval(0)), rot)
        sites[28+i] = rotate((k*c, k*s), rot)
        witnesses[36+i] = rotate((c, s), rot)
        witnesses[43+i] = rotate(((k-1)*c, (k-1)*s), rot)
        witnesses[50+i] = rotate((3*c, s), rot)
        witnesses[57+((i-1) % 7)] = rotate((3*c, -s), rot)
        witnesses[2*i] = rotate((c*(1+k), -s*(k-1)), rot)
        witnesses[2*i+1] = rotate((c*(1+k), s*(k-1)), rot)
        rot = rotate(step, rot)
    incidence = {(v, p) for v, p, _ in edges}
    closest_extra = None
    for v, (vx, vy) in witnesses.items():
        for p, (px, py) in sites.items():
            d2 = square(vx-px) + square(vy-py)
            if (v, p) in incidence:
                if not d2.lo <= 1 <= d2.hi:
                    raise ArithmeticError(f"wrong incidence at {v}, {p}")
            else:
                if d2.lo <= 1:
                    raise ArithmeticError(f"extra incidence at {v}, {p}")
                closest_extra = d2.lo if closest_extra is None else min(closest_extra, d2.lo)
    print(f"All witness-to-nonincident-site squared distances > {float(closest_extra):.6f}")


def reduce_to_boundary(edges):
    rows = [[interval(0) for _ in range(64)] for _ in range(64)]
    for v, p, weight in edges:
        if weight.lo <= 0 or rows[v][p].hi != 0:
            raise ArithmeticError("invalid edge weight or repeated edge")
        rows[v][p] = rows[p][v] = rounded(weight)

    active = set(range(64))
    for v in (*range(36, 64), *range(14, 36)):
        active.remove(v)
        neighbors = sorted(p for p in active if rows[v][p].hi > 0)
        total = sum(rows[v][p] for p in neighbors)
        if total.lo <= 0:
            raise ArithmeticError("nonpositive total conductance")
        for i, p in enumerate(neighbors):
            share = rounded(rows[v][p] / total)
            for q in neighbors[i+1:]:
                conductance = rounded(rows[p][q] + share*rows[v][q])
                rows[p][q] = rows[q][p] = conductance
    return [row[:14] for row in rows[:14]]


def trig(angle):
    sine, cosine = sin(angle/4), cos(angle/4)
    for _ in range(2):
        sine, cosine = rounded(2*sine*cosine), rounded(square(cosine)-square(sine))
    return sine, cosine


def taylor_coefficient(steps, target, limit):
    if steps == 7:
        return interval(-1)

    sine, cosine = trig(target)
    lower = max(Q(0), (2*PI-(14-steps)*limit).lo)
    upper = steps*limit
    right = upper-target
    deviations = Interval((lower-target).lo, right.hi)
    cube = Interval(deviations.lo**3, deviations.hi**3)
    derivative = -sine/3 - cosine*deviations/6 + sine*square(deviations)/20 - cube/90
    if derivative.hi >= 0:
        raise ArithmeticError(f"Taylor bound not decreasing for {steps} steps")
    return cosine - sine*right/3 - cosine*square(right)/12 + sine*square(right)*right/60 - square(square(right))/360


def positive_definite_check(rows, theta, phi, limit):
    angles = [2*i*theta+sign*phi for i in range(7) for sign in (-1, 1)]
    lower = [[Q(0) for _ in angles] for _ in angles]
    scale = 10**24
    for i in range(14):
        for j in range(i+1, 14):
            steps = j-i
            target = angles[j]-angles[i]
            if steps > 7:
                steps = 14-steps
                target = 2*PI-target
            h = taylor_coefficient(steps, target, limit)
            bound = Q(((h*rows[i][j]).lo*scale).__floor__(), scale)
            lower[i][i] += bound
            lower[j][j] += bound
            lower[i][j] -= bound
            lower[j][i] -= bound

    # Gauge d_0=0, since adding a constant to the angles rotates everything.
    pivots = []
    for i in range(1, 14):
        pivot = lower[i][i]
        if pivot <= 0:
            raise ArithmeticError(f"nonpositive symmetric elimination pivot {i}")
        pivots.append(pivot)
        for j in range(i+1, 14):
            share = lower[j][i] / pivot
            for l in range(j, 14):
                lower[j][l] -= share*lower[i][l]
                lower[l][j] = lower[j][l]
    print(f"Taylor lower matrix positive definite after fixing d_0=0. Min pivot {float(min(pivots)):.8g}")


def check():
    theta = PI/7
    c, s = rounded(cos(theta)), rounded(sin(theta))
    k = 4*square(c)
    R = sqrt(1-2*k+2*square(k))
    phi = rounded(asin(s*(k-1)/R))
    limit = rounded(2*asin(1/R))
    edges = graph(k)
    check_incidences(c, s, k, edges)
    rows = reduce_to_boundary(edges)
    positive_definite_check(rows, theta, phi, limit)


if __name__ == '__main__':
    check()
