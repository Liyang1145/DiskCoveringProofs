"""Construct and improve coverings numerically. Use verify_upper.py for proof."""

import argparse
import json
import os
from itertools import combinations
from pathlib import Path

os.environ["OPENBLAS_NUM_THREADS"] = "1"
os.environ["OMP_NUM_THREADS"] = "1"

import numpy as np
from scipy.optimize import minimize
from scipy.spatial import Delaunay


N = 26
PAIRS = np.array(list(combinations(range(N), 2)))


def dot(a, b):
    return np.einsum("...i,...i->...", a, b)


def cross(a, b):
    return a[..., 0] * b[..., 1] - a[..., 1] * b[..., 0]


def rot(a):
    return np.stack((-a[..., 1], a[..., 0]), axis=-1)


def circum(a, b):
    det = cross(a, b)
    rel = (dot(b, b)[:, None] * rot(a) - dot(a, a)[:, None] * rot(b))
    return rel / (2 * det[:, None])


def critical_points(points):
    """A superset of the exact maximizer candidates (computed in doubles)."""
    tri = Delaunay(points).simplices
    a, b, c = points[tri].transpose(1, 0, 2)
    cc = a + circum(b - a, c - a)
    cc = cc[dot(cc, cc) <= 1 + 1e-12]
    p, q = points[PAIRS].transpose(1, 0, 2)
    normal = q - p
    length2 = dot(normal, normal)
    h = (dot(q, q) - dot(p, p)) / 2
    keep = (h * h <= length2) & (length2 > 0)
    normal, h, length2 = normal[keep], h[keep], length2[keep]
    base = (h / length2)[:, None] * normal
    step = np.sqrt(np.maximum(0, length2 - h * h))[:, None] / length2[:, None] * rot(normal)
    lengths = np.linalg.norm(points, axis=1)
    stationary = points[lengths > 0] / lengths[lengths > 0, None]
    return np.concatenate((cc, base + step, base - step, stationary, -stationary, [[1, 0]]))


def measure(points):
    dx = critical_points(points)[:, None, :] - points
    return np.sqrt(dot(dx, dx).min(axis=1).max())


def ring(n, radius, phase):
    angles = (np.arange(n) + phase) * (2 * np.pi / n)
    return radius * np.stack((np.cos(angles), np.sin(angles)), axis=-1)


def seed(k, j, rng, perturb):
    l = N - k - j
    outer_radius = np.clip(np.cos(np.pi / k) - np.sqrt(.25 ** 2 - np.sin(np.pi / k) ** 2), .81, .92)
    outer = ring(k, outer_radius, 0)
    middle = ring(j, .51 + .025 * rng.random(), rng.random())
    core = ring(l, 0 if l == 1 else .115 + .021 * l, rng.random())
    points = np.vstack((outer, middle, core))
    return points + rng.normal(0, perturb, size=points.shape)


def mesh_fit(points, k, iterations=180):
    tri = Delaunay(points).simplices
    tri = tri[(tri >= k).any(axis=1)]
    ntri = len(tri)
    edge = np.arange(k)
    sites = np.column_stack((edge, np.roll(edge, -1))).ravel()
    breaks = np.repeat(edge, 2)
    nrows = ntri + 2 * k
    rows = np.arange(ntri)
    erows = np.arange(ntri, nrows)
    vars_count = 2 * N + k + 1
    theta = (np.arange(k) + .5) * (2 * np.pi / k)
    jacobian = np.zeros((nrows, vars_count))
    jacobian[:, -1] = 1

    def constraints(x):
        p = x[: 2 * N].reshape(N, 2)
        r2 = x[-1]
        t = x[2 * N : -1]
        bpts = np.stack((np.cos(t), np.sin(t)), axis=1)
        offset = bpts[breaks] - p[sites]
        jacobian[erows, 2 * sites] = 2 * offset[:, 0]
        jacobian[erows, 2 * sites + 1] = 2 * offset[:, 1]
        jacobian[erows, 2 * N + breaks] = -2 * dot(offset, rot(bpts[breaks]))

        a, b, c = p[tri].transpose(1, 0, 2)
        ab, ac, bc = b - a, c - a, c - b
        lengths2 = np.stack((dot(bc, bc), dot(ac, ac), dot(ab, ab)), axis=1)
        longest = lengths2.argmax(axis=1)
        diameter2 = lengths2[rows, longest]
        obtuse = 2 * diameter2 >= lengths2.sum(axis=1)
        rel = np.empty_like(ab)
        weights = np.zeros((ntri, 3))
        if obtuse.any():
            weights[obtuse] = .5
            weights[rows[obtuse], longest[obtuse]] = 0
            rel[obtuse] = (
                weights[obtuse, 1, None] * ab[obtuse]
                + weights[obtuse, 2, None] * ac[obtuse]
            )
        acute = ~obtuse
        if acute.any():
            aa, bb = ab[acute], ac[acute]
            rel[acute] = circum(aa, bb)
            det = cross(aa, bb)
            weights[acute, 1] = cross(rel[acute], bb) / det
            weights[acute, 2] = cross(aa, rel[acute]) / det
            weights[acute, 0] = 1 - weights[acute, 1] - weights[acute, 2]
        tdist2 = np.where(obtuse, diameter2 / 4, dot(rel, rel))
        for vertex, d in enumerate((rel, rel - ab, rel - ac)):
            jacobian[rows, 2 * tri[:, vertex]] = 2 * weights[:, vertex] * d[:, 0]
            jacobian[rows, 2 * tri[:, vertex] + 1] = 2 * weights[:, vertex] * d[:, 1]
        return r2 - np.concatenate((tdist2, dot(offset, offset)))

    def jac(x):
        constraints(x)
        return jacobian

    objgrad = np.zeros(vars_count)
    objgrad[-1] = 1
    delta = .62 * 2 * np.pi / k
    x = np.concatenate((points.ravel(), theta, [.33 ** 2]))
    result = minimize(
        lambda z: z[-1],
        x,
        jac=lambda z: objgrad,
        method="SLSQP",
        bounds=[(-1, 1)] * (2 * N) + list(zip(theta - delta, theta + delta)) + [(.17 ** 2, .7 ** 2)],
        constraints=[{"type": "ineq", "fun": constraints, "jac": jac}],
        options={"maxiter": iterations, "ftol": 2e-13},
    )
    return result.x[: 2 * N].reshape(N, 2)


def write_certificate(path, points, radius, source):
    # Search estimates are not certificates until the exact verifier passes.
    scale = 10 ** 14
    radius = np.ceil((radius + 2e-13) * scale) / scale
    payload = {
        "radius": f"{radius:.14f}",
        "centers": [[f"{v:.15f}" for v in p] for p in points],
        "source": source,
    }
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--starts", type=int, default=200)
    parser.add_argument("--seed", type=int, default=2601)
    parser.add_argument("--k", type=int, nargs="+", default=range(14, 19))
    parser.add_argument("--initial", type=Path)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--perturb", type=float, default=.026)
    args = parser.parse_args()
    rng = np.random.default_rng(args.seed)
    best = np.inf
    branch_best = {}
    initial = None
    if args.initial:
        initial = np.array(json.loads(args.initial.read_text(encoding="utf-8"))["centers"], dtype=float)
    for i in range(args.starts):
        k = args.k[i % len(args.k)]
        j = int(rng.integers(max(5, N - k - 4), min(10, N - k - 1) + 1))
        if initial is not None:
            points = initial.copy()
            if i:
                points += rng.normal(0, args.perturb, size=points.shape)
        else:
            points = seed(k, j, rng, args.perturb if i >= len(args.k) else 0)
        for _ in range(3):
            trial = mesh_fit(points, k)
            score = measure(trial)
            if score < branch_best.get(k, np.inf):
                branch_best[k] = score
                print(f"i={i} k={k} j={j} r={score:.16f}", flush=True)
            if score < best:
                best = score
                write_certificate(args.out, trial, score, {"seed": args.seed, "start": i, "k": k, "j": j})
            if np.max(np.abs(trial - points)) < 1e-7:
                break
            points = trial
    print("Branch best (numerical only):", branch_best, flush=True)


if __name__ == "__main__":
    main()
