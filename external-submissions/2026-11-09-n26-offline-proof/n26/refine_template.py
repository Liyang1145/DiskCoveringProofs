"""Refine the contact template discovered by search.py (numerical only)."""

import argparse
import json
from decimal import Decimal as D, ROUND_CEILING, getcontext
from pathlib import Path


def add(p, q):
    return p[0] + q[0], p[1] + q[1]


def sub(p, q):
    return p[0] - q[0], p[1] - q[1]


def dot(p, q):
    return p[0] * q[0] + p[1] * q[1]


def reflect(p, axis):
    f = 2 * dot(p, axis) / dot(axis, axis)
    return f * axis[0] - p[0], f * axis[1] - p[1]


def template(r, d, k, with_seams=False):
    zero = r * 0
    a = (1 - r * r).sqrt()
    v = (r * r - d * d).sqrt()
    q0 = k + 2 * d
    q2 = r + (r * r - k * k).sqrt()
    p0 = (a, zero)
    p1 = ((a + q0) / 2, r + (r * r - ((a - q0) / 2) ** 2).sqrt())
    y0 = (a, r)
    y1 = reflect(y0, p1)
    p2 = add(y1, (-d, v))
    y2 = reflect(y1, p2)
    y3 = (d, (1 - d * d).sqrt())
    p4y = y3[1] - v
    p3 = (d + (r * r - ((p4y - q2) / 2) ** 2).sqrt(), v + (p4y + q2) / 2)
    p4 = (zero, p4y)
    residual = dot(sub(y2, p3), sub(y2, p3)) - r * r
    result = residual, (p0, p1, p2, p3, p4), ((q0, zero), (k + d, r + v), (zero, q2)), (k, zero)
    return (*result, (y0, y1, y2, y3)) if with_seams else result


def perturb(z, i, delta):
    return tuple(a + delta if j == i else a for j, a in enumerate(z))


def residual(z):
    return template(*z)[0]


def system(z):
    step = D("1e-32")
    partial = [
        (residual(perturb(z, i, step)) - residual(perturb(z, i, -step))) / (2 * step)
        for i in (1, 2)
    ]
    return (residual(z), *partial)


def solve_linear(a, b):
    m = [list(row) + [val] for row, val in zip(a, b)]
    for i in range(len(m)):
        j = max(range(i, len(m)), key=lambda j: abs(m[j][i]))
        m[i], m[j] = m[j], m[i]
        pivot = m[i][i]
        m[i] = [v / pivot for v in m[i]]
        for j in range(len(m)):
            if j != i:
                v = m[j][i]
                m[j] = [t - v * u for t, u in zip(m[j], m[i])]
    return tuple(row[-1] for row in m)


def solve(r, d, k):
    z = (r, d, k)
    step = D("1e-19")
    for _ in range(8):
        columns = []
        for i in range(3):
            p = system(perturb(z, i, step))
            q = system(perturb(z, i, -step))
            columns.append(tuple((a - b) / (2 * step) for a, b in zip(p, q)))
        change = solve_linear(zip(*columns), system(z))
        z = tuple(a - b for a, b in zip(z, change))
    return z


def ring(quadrant):
    pts = []
    for xsign, ysign, qs in ((1, 1, quadrant[:-1]), (-1, 1, quadrant[:0:-1]),
                            (-1, -1, quadrant[:-1]), (1, -1, quadrant[:0:-1])):
        pts.extend((xsign * x, ysign * y) for x, y in qs)
    return pts


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--digits", type=int, default=55)
    args = parser.parse_args()
    getcontext().prec = 100
    r, d, k = solve(D("0.2347000904004482"), D("0.20556460"), D("0.13840802"))
    print("Numerical stationary template parameters:")
    print("r =", r)
    print("d =", d)
    print("k =", k)
    print("Residuals:", *system((r, d, k)))
    unit = D(1).scaleb(-args.digits)
    # The certificate verifies this rounded arrangement independently.
    u = (r + 2 * unit).quantize(unit, rounding=ROUND_CEILING)
    _, outer, middle, core = template(r, d, k)
    points = ring(outer) + ring(middle) + [core, (-core[0], core[1])]
    data = {
        "radius": str(u),
        "centers": [[str(a.quantize(unit)) for a in p] for p in points],
        "source": "The numerically refined symmetric contact template found by search.py",
    }
    args.out.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
