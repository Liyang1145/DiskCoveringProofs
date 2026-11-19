"""Exact coverage certificate for twelve equal disks arranged in six wedges."""
from fractions import Fraction as Q

def sign(a, b):
    """Return the sign of a + b sqrt(3), for rational a and b."""
    if a == 0:
        return (b > 0) - (b < 0)
    if b == 0 or (a > 0) == (b > 0):
        return (a > 0) - (a < 0)
    v = a*a - 3*b*b
    return ((v > 0) - (v < 0))*((a > 0) - (a < 0))

def sq_distance(p, q):
    real, radical = Q(0), Q(0)
    for (a, b), (c, d) in zip(p, q):
        x, y = a-c, b-d
        real += x*x + 3*y*y
        radical += 2*x*y
    return real, radical

def point(x, y):
    return (Q(x), Q(0)), (Q(y), Q(0))

def on_sixty_degree_ray(radius):
    t = Q(radius)/2
    return (t, Q(0)), (Q(0), t)

def certify_upper():
    r = Q("0.361102963745")
    u = "0.278241660874428"
    v = "0.769169019163405"
    i = point(u, 0)
    h = point("0.819672312309468", "0.312853440890865")
    l = on_sixty_degree_ray(v)

    o = point(0, 0)
    a = on_sixty_degree_ray("0.408066055418896")
    b = point("0.639344624618937", 0)
    m = point("0.458628785034067", "0.312750578905087")
    p = point(1, 0)
    t = Q("0.381681113528630")
    q = point((1-t*t)/(1+t*t), 2*t/(1+t*t))
    s = on_sixty_degree_ray(1)

    for x, y in (h, m, q):
        assert x[0] > 0 and y[0] > 0 and y[0]**2 < 3*x[0]**2
    assert sign(*sq_distance(m, o)) > 0
    real, radical = sq_distance(m, o)
    assert sign(1-real, -radical) > 0
    assert 0 < Q("0.408066055418896") < 1
    assert 0 < b[0][0] < 1
    assert sq_distance(q, o) == (1, 0)

    for label, center, vertices in (
        ("inner", i, (o, a, m, b)),
        ("outer nearer", l, (a, m, q, s)),
        ("outer farther", h, (b, m, q, p)),
    ):
        for vertex in vertices:
            real, radical = sq_distance(center, vertex)
            assert sign(r*r - real, -radical) >= 0
        print(f"{label}: all four vertex inequalities verified")

if __name__ == "__main__":
    certify_upper()
