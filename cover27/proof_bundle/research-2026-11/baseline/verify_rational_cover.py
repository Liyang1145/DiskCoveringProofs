"""Exact continuous covering check for rational centers in a unit disk."""
import argparse
from fractions import Fraction as F
from itertools import combinations
import json
from math import isqrt
from pathlib import Path


def norm(p):
    return p[0]**2 + p[1]**2


def difference(p, q):
    return p[0] - q[0], p[1] - q[1]


def dot(p, q):
    return p[0] * q[0] + p[1] * q[1]


def sqrt_interval(a):
    scale = 10**36
    low = isqrt(a.numerator * scale**2 // a.denominator)
    return F(low, scale), F(low + 1, scale)


def point(p):
    return (p[0], p[0]), (p[1], p[1])


def line_segment_box(base, direction, scale):
    box = []
    for a, b in zip(base, direction):
        ends = [a + b * t for t in scale]
        box.append((min(ends), max(ends)))
    return tuple(box)


def distance_upper(box, center):
    return sum(max((a - x)**2, (b - x)**2) for (a, b), x in zip(box, center))


def critical_boxes(centers):
    norms = tuple(map(norm, centers))
    for i, j, k in combinations(range(len(centers)), 3):
        u = difference(centers[j], centers[i])
        v = difference(centers[k], centers[i])
        d = 2 * (u[0] * v[1] - u[1] * v[0])
        if d == 0:
            continue
        h, l = norms[j] - norms[i], norms[k] - norms[i]
        q = ((h * v[1] - l * u[1]) / d, (u[0] * l - v[0] * h) / d)
        if norm(q) <= 1:
            yield "interior triple", point(q)

    for i, j in combinations(range(len(centers)), 2):
        u = difference(centers[j], centers[i])
        u2 = norm(u)
        k = (norms[j] - norms[i]) / 2
        q = (k * u[0] / u2, k * u[1] / u2)
        radicand = (1 - norm(q)) / u2
        if radicand < 0:
            continue
        scale = sqrt_interval(radicand)
        for v in ((-u[1], u[0]), (u[1], -u[0])):
            yield "boundary bisector", line_segment_box(q, v, scale)

    for center, t in zip(centers, norms):
        if t:
            yield "boundary stationary point", line_segment_box((0, 0), center, sqrt_interval(1 / t))
            yield "boundary stationary point", line_segment_box((0, 0), (-center[0], -center[1]), sqrt_interval(1 / t))
    yield "reference boundary point", point((F(1), F(0)))


def verify(path):
    data = json.loads(path.read_text(encoding="utf-8"))
    centers = [tuple(map(F, p)) for p in data["centers"]]
    n = data["n"]
    r = F(data["radius"])
    if n <= 0 or len(centers) != n or len(set(centers)) != n or r <= 0:
        raise ValueError("invalid rational configuration")
    if any(len(p) != 2 or norm(p) >= 1 for p in centers):
        raise ValueError("centers must be interior to the unit disk")
    counts = {}
    for typ, box in critical_boxes(centers):
        if not any(distance_upper(box, c) < r*r for c in centers):
            raise ValueError(f"no covering center for {typ}: {box}")
        counts[typ] = counts.get(typ, 0) + 1
    print(f"PASS: {n} rational disks of radius {data['radius']} cover the closed unit disk.")
    for typ, count in counts.items():
        print(f"  {typ}: {count}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("cover", type=Path)
    verify(parser.parse_args().cover)
