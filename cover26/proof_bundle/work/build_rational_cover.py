"""Generate an exact dyadic-square cover of the closed unit disk.

The only floating input is used to CHOOSE rational centers. All proof decisions
after quantization use integers, and the independent verifier uses Fraction.
"""

import argparse
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import time

import numpy as np


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def publish(path, data):
    if path.exists():
        raise FileExistsError(path)
    path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--centers", type=Path, required=True)
    parser.add_argument("--radius", default="234701/1000000")
    parser.add_argument("--denominator", type=int, default=10**10)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--max-depth", type=int, default=28)
    parser.add_argument("--node-limit", type=int, default=1000000)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    c = np.load(args.centers)
    if c.shape != (26, 2) or not np.isfinite(c).all() or args.denominator < 1:
        raise ValueError("expected 26 finite centers")
    C = args.denominator
    centers = [[int(round(float(value) * C)) for value in row] for row in c]
    radius = F(args.radius)
    if not 0 < radius < 1:
        raise ValueError("invalid radius")
    p, q = radius.numerator, radius.denominator
    stack = [(0, 0, 0)]
    leaves, calls, covered, outside, depth_max = [], 0, 0, 0, 0
    started = time.monotonic()
    while stack:
        d, i, j = stack.pop()
        calls += 1
        if calls > args.node_limit:
            raise RuntimeError("node limit: no complete cover certificate")
        L = 1 << d
        xl, xh = 2 * i - L, 2 * (i + 1) - L
        yl, yh = 2 * j - L, 2 * (j + 1) - L
        mx, my = max(xl, -xh, 0), max(yl, -yh, 0)
        if mx * mx + my * my > L * L:
            leaves.append({"depth": d, "i": i, "j": j, "kind": "outside"})
            outside += 1
            depth_max = max(depth_max, d)
            continue
        cx, cy = 2 * i + 1 - L, 2 * j + 1 - L
        order = sorted(range(26), key=lambda k: (
            (centers[k][0] * L - C * cx) ** 2 +
            (centers[k][1] * L - C * cy) ** 2
        ))
        chosen = None
        for k in order[:4]:
            a, b = centers[k]
            dx = max(abs(a * L - C * xl), abs(a * L - C * xh))
            dy = max(abs(b * L - C * yl), abs(b * L - C * yh))
            if (dx * dx + dy * dy) * q * q <= p * p * C * C * L * L:
                chosen = k
                break
        if chosen is not None:
            leaves.append({"depth": d, "i": i, "j": j,
                           "kind": "covered", "center": chosen})
            covered += 1
            depth_max = max(depth_max, d)
            continue
        if d == args.max_depth:
            raise RuntimeError(f"depth limit at {(d, i, j)}: no complete cover certificate")
        for u, v in ((1, 1), (1, 0), (0, 1), (0, 0)):
            stack.append((d + 1, 2 * i + u, 2 * j + v))
    args.output.mkdir(parents=True)
    geometry = {
        "schema": "N26-exact-rational-center-cover-v1", "N": 26,
        "radius": str(radius), "centers_denominator": C, "center_numerators": centers,
        "radius_is_sharp": False, "global_optimality_proved": False,
    }
    publish(args.output / "geometry.json", geometry)
    certificate = {
        "schema": "exact-dyadic-unit-disk-cover-v1",
        "geometry_sha256": sha(args.output / "geometry.json"),
        "leaves": leaves,
    }
    publish(args.output / "cover-certificate.json", certificate)
    publish(args.output / "BUILD.json", {
        "schema": "N26-rational-cover-builder-run-v1",
        "complete": True, "calls": calls, "leaves": len(leaves),
        "covered_leaves": covered, "outside_leaves": outside,
        "max_depth": depth_max, "seconds": time.monotonic() - started,
        "all_acceptance_decisions_integer_only": True,
        "global_optimality_proved": False,
        "files": {str(path): sha(path) for path in (
            Path(__file__), args.centers, args.output / "geometry.json",
            args.output / "cover-certificate.json")},
    })
    print(json.dumps({"complete": True, "radius": str(radius), "calls": calls,
                      "covered_leaves": covered, "outside_leaves": outside,
                      "max_depth": depth_max}), flush=True)


if __name__ == "__main__":
    main()
