from itertools import combinations

# Coordinates and radii use the integer unit 10^-36.
U = 10**36
R = 361102963744508644113087702017065184
CENTERS = [
    (278241660874427912148631022898478810, 0),
    (-139120830437213956074315511449239405, 240964346708429276942593788413017681),
    (-139120830437213956074315511449239405, -240964346708429276942593788413017681),
    (384584509581702546649884672158797773, 666119910399468523302307092517667851),
    (-769169019163405093299769344317595547, 0),
    (384584509581702546649884672158797773, -666119910399468523302307092517667851),
    (819672312309468278130859362457771996, 312853440890865028703115138750594947),
    (-680775183627596534374456155363531418, 553430324793299251390167163145818396),
    (-138897128681871743756403207094240578, -866283765684164280093282301896413342),
    (819672312309468278130859362457771996, -312853440890865028703115138750594947),
    (-138897128681871743756403207094240578, 866283765684164280093282301896413342),
    (-680775183627596534374456155363531418, -553430324793299251390167163145818396),
]


def norm2(p):
    return p[0]**2 + p[1]**2


def dot(p, q):
    return p[0] * q[0] + p[1] * q[1]


def sub(p, q):
    return p[0] - q[0], p[1] - q[1]


def det(p, q):
    return p[0] * q[1] - p[1] * q[0]


def nonpositive(a, b, k):
    # Decide a + b sqrt(k) <= 0 by exact integers, k >= 0.
    if b == 0 or k == 0:
        return a <= 0
    if b > 0:
        return a <= 0 and b*b*k <= a*a
    return a <= 0 or a*a <= b*b*k


def check(centers=CENTERS):
    assert len(centers) == len(set(centers)) == 12 and all(norm2(c) for c in centers)
    triple_count = boundary_count = 0
    for p, q, v in combinations(centers, 3):
        h, j = sub(q, p), sub(v, p)
        denominator = 2 * det(h, j)
        if denominator == 0:
            continue
        f, g = norm2(q) - norm2(p), norm2(v) - norm2(p)
        x, y = f*j[1] - g*h[1], h[0]*g - j[0]*f
        if x*x + y*y > (U*denominator)**2:
            continue
        assert any((x - denominator*c[0])**2 + (y - denominator*c[1])**2
                   <= (R*denominator)**2 for c in centers)
        triple_count += 1

    for p, q in combinations(centers, 2):
        d = sub(q, p)
        s = norm2(d)
        n = norm2(q) - norm2(p)
        k = 4*s*U*U - n*n
        if k < 0:
            continue
        perp = -d[1], d[0]
        for sign in (-1, 1):
            assert any(nonpositive(s*(U*U + norm2(c) - R*R) - n*dot(d, c),
                                   sign*dot(perp, c), k) for c in centers)
            boundary_count += 1
    for h in centers:
        # x = -U h / sqrt(dot(h,h)).
        k = norm2(h)
        assert any(nonpositive(2*U*dot(h,c), U*U + norm2(c) - R*R, k) for c in centers)
    print('upper bound verified using integer arithmetic')
    print('radius =', R, '/', U)
    print('interior circumcenters, boundary bisector intersections, antipodes =',
          triple_count, boundary_count, len(centers))


if __name__ == '__main__':
    check()
