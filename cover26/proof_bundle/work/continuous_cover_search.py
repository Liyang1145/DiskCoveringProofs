"""Floating continuous-critical-point search; never a covering certificate."""

import argparse
import hashlib
from itertools import combinations
import json
import math
from pathlib import Path
import time

import numpy as np
from scipy.optimize import minimize


BASE = Path(__file__).resolve().parent
INDEX_CACHE = {}


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def index_arrays(n):
    if n not in INDEX_CACHE:
        pairs = np.asarray(list(combinations(range(n), 2)), dtype=int).reshape(-1, 2)
        triples = np.asarray(list(combinations(range(n), 3)), dtype=int).reshape(-1, 3)
        INDEX_CACHE[n] = pairs, triples
    return INDEX_CACHE[n]


def critical_points(centers):
    """All triple circumcenters in D, pair-bisector/unit-circle intersections,
    radial circle stationary points, plus fixed boundary points.

    Near degeneracies are handled numerically; the result is NOT rigorous.
    """
    c = np.asarray(centers, dtype=float)
    n = len(c)
    if c.shape != (n, 2) or n == 0 or not np.isfinite(c).all():
        raise ValueError("nonempty finite plane centers required")
    pairs, triples = index_arrays(n)
    rows = [np.asarray([[0., 0.], [1., 0.], [-1., 0.], [0., 1.], [0., -1.]])]
    norms = np.linalg.norm(c, axis=1)
    active = norms > 1e-14
    unit = c[active] / norms[active, None]
    rows.extend((unit, -unit))
    squares = (c * c).sum(axis=1)
    if len(pairs):
        i, j = pairs.T
        d = c[j] - c[i]
        nn = (d * d).sum(axis=1)
        h = (squares[j] - squares[i]) / 2
        valid = nn > 1e-24
        d, nn, h = d[valid], nn[valid], h[valid]
        radicand = 1 - h * h / nn
        valid = radicand >= -1e-13
        d, nn, h, radicand = d[valid], nn[valid], h[valid], radicand[valid]
        mid = (h / nn)[:, None] * d
        side = np.column_stack((-d[:, 1], d[:, 0])) / np.sqrt(nn)[:, None]
        offset = np.sqrt(np.maximum(0., radicand))[:, None] * side
        rows.extend((mid + offset, mid - offset))
    if len(triples):
        i, j, k = triples.T
        u, v = c[j] - c[i], c[k] - c[i]
        det = u[:, 0] * v[:, 1] - u[:, 1] * v[:, 0]
        valid = np.abs(det) > 1e-14
        i, j, k, u, v, det = i[valid], j[valid], k[valid], u[valid], v[valid], det[valid]
        h, g = (squares[j] - squares[i]) / 2, (squares[k] - squares[i]) / 2
        vertices = np.column_stack(((h * v[:, 1] - u[:, 1] * g) / det,
                                    (u[:, 0] * g - h * v[:, 0]) / det))
        rows.append(vertices[(vertices * vertices).sum(axis=1) <= 1 + 1e-13])
    return np.unique(np.round(np.vstack(rows), 14), axis=0)


def distances(centers, points):
    ds = ((points[:, None, :] - centers[None, :, :]) ** 2).sum(axis=2)
    owners = ds.argmin(axis=1)
    return ds[np.arange(len(points)), owners], owners


def audit(centers):
    points = critical_points(centers)
    ds, owners = distances(centers, points)
    return float(np.sqrt(ds.max())), points, ds, owners


def constraints_and_jacobian(z, points, owners, n):
    c = z[:-1].reshape(n, 2)
    delta = points - c[owners]
    value = z[-1] - (delta * delta).sum(axis=1)
    jac = np.zeros((len(points), 2 * n + 1))
    rows = np.arange(len(points))
    jac[rows, 2 * owners] = 2 * delta[:, 0]
    jac[rows, 2 * owners + 1] = 2 * delta[:, 1]
    jac[:, -1] = 1.
    return value, jac


def refine(initial, iterations=65):
    centers = initial.copy()
    n = len(centers)
    best_r, points, ds, owners = audit(centers)
    history = []
    stored = np.empty((0, 2))
    stalls = 0
    for iteration in range(iterations):
        chosen = np.argsort(ds)[-160:]
        stored = np.unique(np.vstack((stored, points[chosen])).round(11), axis=0)
        # Old witnesses remain valid points in D; keep the most relevant ones.
        stored_ds, stored_owners = distances(centers, stored)
        selected = np.argsort(stored_ds)[-500:]
        active = stored[selected]
        assignments = stored_owners[selected]
        z = np.concatenate((centers.ravel(), [best_r * best_r + 1e-10]))
        step = 0.045 if iteration < 15 else 0.025
        bounds = [(max(-1.1, value - step), min(1.1, value + step))
                  for value in centers.ravel()] + [(0.0, 1.0)]
        gradient = np.zeros_like(z)
        gradient[-1] = 1.
        result = minimize(
            lambda x: float(x[-1]), z,
            jac=lambda x: gradient,
            method="SLSQP", bounds=bounds,
            constraints={
                "type": "ineq",
                "fun": lambda x: constraints_and_jacobian(x, active, assignments, n)[0],
                "jac": lambda x: constraints_and_jacobian(x, active, assignments, n)[1],
            },
            options={"maxiter": 100, "ftol": 1e-12, "disp": False},
        )
        proposed = result.x[:-1].reshape(n, 2)
        candidate_r, candidate = best_r, centers
        for fraction in (1., .5, .25, .125, .0625):
            trial = centers + fraction * (proposed - centers)
            radius, _, _, _ = audit(trial)
            if radius < candidate_r:
                candidate_r, candidate = radius, trial
        improvement = best_r - candidate_r
        centers, best_r = candidate.copy(), candidate_r
        best_r, points, ds, owners = audit(centers)
        stalls = stalls + 1 if improvement < 1e-10 else 0
        history.append({"iteration": iteration, "floating_radius": best_r,
                        "constraints": len(active), "optimizer_success": bool(result.success),
                        "improvement": improvement})
        if stalls >= 6:
            break
    return centers, best_r, history


def lattice_seed(rng):
    step = rng.uniform(.38, .43)
    phase = rng.uniform(0, math.pi / 3)
    rotation = np.asarray([[math.cos(phase), -math.sin(phase)],
                           [math.sin(phase), math.cos(phase)]])
    shift = rng.uniform(-.13, .13, size=2)
    points = np.asarray([[step * (i + j / 2), step * math.sqrt(3) * j / 2]
                         for i in range(-5, 6) for j in range(-5, 6)])
    points = points @ rotation.T + shift
    return points[np.argsort((points * points).sum(axis=1))[:26]]


def seeds(base, count):
    rng = np.random.default_rng(260910)
    out = []
    initial = np.vstack((base, [.12, .02]))
    out.append(("split-origin", initial.copy()))
    initial[16] = [.10, 0.]
    initial[-1] = [-.10, 0.]
    out.append(("symmetric-split-origin", initial.copy()))
    for index, offset in ((17, [0., .10]), (0, [0., .12]), (1, [.06, -.08])):
        c = np.vstack((base, base[index] - offset))
        c[index] += offset
        out.append((f"split-center-{index}", c))
    for j in range(count - len(out)):
        if j % 3 == 2:
            c = lattice_seed(rng)
            tag = f"hexagonal-{j}"
        else:
            c = np.vstack((base, rng.uniform(-.6, .6, size=2)))
            c += rng.normal(0., .025 if j % 3 == 0 else .075, c.shape)
            tag = f"perturbed-{j}"
        norms = np.linalg.norm(c, axis=1)
        c *= np.minimum(1., .99 / np.maximum(norms, 1e-15))[:, None]
        out.append((tag, c))
    return out[:count]


def calibration(base):
    examples = [
        ("one-origin", np.zeros((1, 2)), 1.),
        ("duplicate-origins", np.zeros((26, 2)), 1.),
        ("one-offset", np.asarray([[.2, .3]]), 1 + math.hypot(.2, .3)),
        ("two-collinear", np.asarray([[-.5, 0.], [.5, 0.]]), math.sqrt(1.25)),
        ("four-square", np.asarray([[x, y] for x in (-.5, .5) for y in (-.5, .5)]),
         math.sqrt(.5)),
        ("n25-exact-seed", base, 1 / (math.sqrt(6) + math.sqrt(3))),
    ]
    results = []
    for tag, c, expected in examples:
        actual, _, _, _ = audit(c)
        if abs(actual - expected) > 2e-12:
            raise AssertionError((tag, actual, expected))
        results.append({"case": tag, "actual": actual, "expected": expected})
    rng = np.random.default_rng(26)
    c = rng.uniform(-.8, .8, (26, 2))
    p = rng.uniform(-.7, .7, (35, 2))
    _, owners = distances(c, p)
    z = np.concatenate((c.ravel(), [.1]))
    _, analytic = constraints_and_jacobian(z, p, owners, 26)
    error = 0.
    for j in range(len(z)):
        plus, minus = z.copy(), z.copy()
        plus[j] += 1e-6
        minus[j] -= 1e-6
        numeric = (constraints_and_jacobian(plus, p, owners, 26)[0]
                   - constraints_and_jacobian(minus, p, owners, 26)[0]) / 2e-6
        error = max(error, float(np.max(np.abs(numeric - analytic[:, j]))))
    if error > 1e-8:
        raise AssertionError("analytic constraint Jacobian disagrees")
    return {"critical_point_tests": results, "jacobian_max_error": error}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--base", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--starts", type=int, default=18)
    parser.add_argument("--iterations", type=int, default=65)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    base = np.load(args.base)
    if base.shape != (25, 2):
        raise ValueError("expected n25 seed")
    args.output.mkdir(parents=True)
    checks = calibration(base)
    (args.output / "CALIBRATION.json").write_text(json.dumps(checks, indent=2) + "\n")
    rows, best, best_centers = [], float("inf"), None
    for i, (tag, seed) in enumerate(seeds(base, args.starts)):
        started = time.monotonic()
        c, radius, history = refine(seed, args.iterations)
        row = {"index": i, "seed": tag, "floating_radius": radius,
               "seconds": time.monotonic() - started, "history": history}
        rows.append(row)
        np.save(args.output / f"centers-{i:03d}.npy", c)
        (args.output / f"run-{i:03d}.json").write_text(json.dumps(row, indent=2) + "\n")
        if radius < best:
            best, best_centers = radius, c.copy()
            np.save(args.output / "best-centers.npy", best_centers)
        print(json.dumps({k: v for k, v in row.items() if k != "history"}), flush=True)
    report = {
        "schema": "N26-continuous-critical-point-multistart-numeric-v1",
        "N": 26, "floating_radius": best,
        "continuous_cover_proved": False, "global_optimality_proved": False,
        "calibration_passed": True, "starts": rows,
        "files": {str(p): sha(p) for p in (
            Path(__file__), args.base, args.output / "best-centers.npy")},
        "scope": "Floating candidate discovery only; requires exact covering certification.",
    }
    (args.output / "REPORT.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"best_floating_radius": best, "starts_completed": len(rows),
                      "continuous_cover_proved": False}), flush=True)


if __name__ == "__main__":
    main()
