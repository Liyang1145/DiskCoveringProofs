"""Numerical minimax refinement using derivatives of moving Voronoi vertices."""

import argparse
import json
import math
from pathlib import Path
import time

import numpy as np
from scipy.optimize import minimize

from continuous_cover_search import audit, distances, index_arrays, seeds, sha


def triangle_data(c, ids):
    a, b, d = c[ids[:, 0]], c[ids[:, 1]], c[ids[:, 2]]
    u, v = b - a, d - a
    det = u[:, 0] * v[:, 1] - u[:, 1] * v[:, 0]
    safe = np.where(np.abs(det) > 1e-12, det, np.where(det >= 0, 1e-12, -1e-12))
    h = ((b * b).sum(axis=1) - (a * a).sum(axis=1)) / 2
    g = ((d * d).sum(axis=1) - (a * a).sum(axis=1)) / 2
    p = np.column_stack(((h * v[:, 1] - u[:, 1] * g) / safe,
                         (u[:, 0] * g - h * v[:, 0]) / safe))
    w = p - a
    lb = (w[:, 0] * v[:, 1] - w[:, 1] * v[:, 0]) / safe
    ld = (u[:, 0] * w[:, 1] - u[:, 1] * w[:, 0]) / safe
    weights = np.column_stack((1 - lb - ld, lb, ld))
    r2 = ((p - a) ** 2).sum(axis=1)
    return p, weights, r2, det


def pair_data(c, ids, signs):
    a, b = c[ids[:, 0]], c[ids[:, 1]]
    delta = b - a
    nn = np.maximum((delta * delta).sum(axis=1), 1e-24)
    h = ((b * b).sum(axis=1) - (a * a).sum(axis=1)) / 2
    midpoint = h[:, None] / nn[:, None] * delta
    radicand = 1 - h * h / nn
    side = np.column_stack((-delta[:, 1], delta[:, 0])) / np.sqrt(nn)[:, None]
    p = midpoint + (signs * np.sqrt(np.maximum(1e-15, radicand)))[:, None] * side
    tangent = np.column_stack((-p[:, 1], p[:, 0]))
    ta, tb = (a * tangent).sum(axis=1), (b * tangent).sum(axis=1)
    denominator = ta - tb
    safe = np.where(np.abs(denominator) > 1e-12, denominator,
                    np.where(denominator >= 0, 1e-12, -1e-12))
    la = -tb / safe
    weights = np.column_stack((la, 1 - la))
    r2 = ((p - a) ** 2).sum(axis=1)
    return p, weights, r2, radicand, denominator


def components(c):
    pairs, triples = index_arrays(len(c))
    p, weights, r2, det = triangle_data(c, triples)
    valid = (np.abs(det) > 1e-10) & ((p * p).sum(axis=1) <= 1 + 1e-12)
    valid &= (weights.min(axis=1) >= -1e-9)
    valid_ids = np.flatnonzero(valid)
    if len(valid_ids):
        ds, _ = distances(c, p[valid_ids])
        valid_ids = valid_ids[r2[valid_ids] <= ds + 1e-9]
    tri = triples[valid_ids]

    pair_ids = np.repeat(pairs, 2, axis=0)
    signs = np.tile(np.asarray([1., -1.]), len(pairs))
    p, weights, r2, rad, denominator = pair_data(c, pair_ids, signs)
    valid = (rad > 1e-10) & (np.abs(denominator) > 1e-10)
    valid &= weights.min(axis=1) >= -1e-9
    valid_ids = np.flatnonzero(valid)
    if len(valid_ids):
        ds, _ = distances(c, p[valid_ids])
        valid_ids = valid_ids[r2[valid_ids] <= ds + 1e-9]
    pair_ids, signs = pair_ids[valid_ids], signs[valid_ids]

    norms = np.linalg.norm(c, axis=1)
    radial = np.flatnonzero(norms > 1e-10)
    p = -c[radial] / norms[radial, None]
    ds, owners = distances(c, p)
    radial = radial[(owners == radial) & ((1 + norms[radial]) ** 2 <= ds + 1e-9)]
    return {"triangles": tri, "pairs": pair_ids, "signs": signs, "radial": radial}


def values_gradients(c, desc):
    n = len(c)
    values, jac = [], []
    for ids, evaluate in (
        (desc["triangles"], lambda: triangle_data(c, desc["triangles"])[:3]),
        (desc["pairs"], lambda: pair_data(c, desc["pairs"], desc["signs"])[:3]),
    ):
        if not len(ids):
            continue
        p, weights, r2 = evaluate()
        grad = np.zeros((len(ids), 2 * n))
        rows = np.arange(len(ids))
        for j in range(ids.shape[1]):
            delta = 2 * weights[:, j, None] * (c[ids[:, j]] - p)
            grad[rows, 2 * ids[:, j]] = delta[:, 0]
            grad[rows, 2 * ids[:, j] + 1] = delta[:, 1]
        values.append(r2)
        jac.append(grad)
    ids = desc["radial"]
    if len(ids):
        norms = np.linalg.norm(c[ids], axis=1)
        grad = np.zeros((len(ids), 2 * n))
        delta = 2 * (1 + norms)[:, None] * c[ids] / norms[:, None]
        rows = np.arange(len(ids))
        grad[rows, 2 * ids] = delta[:, 0]
        grad[rows, 2 * ids + 1] = delta[:, 1]
        values.append((1 + norms) ** 2)
        jac.append(grad)
    if not values:
        raise ValueError("no regular active geometric component")
    return np.concatenate(values), np.vstack(jac)


def calibrate(base):
    c = np.vstack((base, [.12, .02]))
    desc = components(c)
    values, analytic = values_gradients(c, desc)
    radius, _, _, _ = audit(c)
    if abs(values.max() - radius * radius) > 1e-10:
        raise AssertionError("moving components miss seed maximum")
    error = 0.
    for j in range(c.size):
        plus, minus = c.copy().ravel(), c.copy().ravel()
        plus[j] += 1e-6
        minus[j] -= 1e-6
        numeric = (values_gradients(plus.reshape(c.shape), desc)[0]
                   - values_gradients(minus.reshape(c.shape), desc)[0]) / 2e-6
        error = max(error, float(np.max(np.abs(numeric - analytic[:, j]))))
    if error > 2e-6:
        raise AssertionError(("moving-vertex derivative failed", error))
    return {"analytic_derivative_max_error": error,
            "seed_components": {key: len(value) for key, value in desc.items()},
            "seed_radius": radius}


def refine(initial, iterations):
    c = initial.copy()
    radius, _, _, _ = audit(c)
    history = []
    stalls = 0
    for iteration in range(iterations):
        desc = components(c)
        values, _ = values_gradients(c, desc)
        # Boundary/tie degeneracies are not certified by this numerical model.
        # Every proposed update is still checked with the full floating auditor.
        z = np.concatenate((c.ravel(), [max(radius * radius, values.max()) + 1e-10]))
        objective_jac = np.zeros_like(z)
        objective_jac[-1] = 1.
        trust = .08 if iteration < 12 else .035
        bounds = [(max(-1.1, value - trust), min(1.1, value + trust)) for value in c.ravel()]
        bounds.append((0., 1.))

        def constraints(x):
            vals, jac = values_gradients(x[:-1].reshape(c.shape), desc)
            return x[-1] - vals

        def constraint_jac(x):
            vals, jac = values_gradients(x[:-1].reshape(c.shape), desc)
            return np.column_stack((-jac, np.ones(len(vals))))

        result = minimize(lambda x: float(x[-1]), z, jac=lambda x: objective_jac,
                          method="SLSQP", bounds=bounds,
                          constraints={"type": "ineq", "fun": constraints, "jac": constraint_jac},
                          options={"maxiter": 180, "ftol": 1e-12, "disp": False})
        proposed = result.x[:-1].reshape(c.shape)
        old_radius, selected, selected_r = radius, c, radius
        for fraction in (1., .5, .25, .125, .0625, .015625):
            trial = c + fraction * (proposed - c)
            value, _, _, _ = audit(trial)
            if value < selected_r:
                selected, selected_r = trial, value
        c, radius = selected.copy(), selected_r
        improvement = old_radius - radius
        stalls = stalls + 1 if improvement < 1e-10 else 0
        history.append({"iteration": iteration, "floating_radius": radius,
                        "components": len(values), "success": bool(result.success),
                        "improvement": improvement})
        if stalls >= 8:
            break
    return c, radius, history


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--base", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--starts", type=int, default=24)
    parser.add_argument("--iterations", type=int, default=90)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    base = np.load(args.base)
    args.output.mkdir(parents=True)
    checks = calibrate(base)
    (args.output / "CALIBRATION.json").write_text(json.dumps(checks, indent=2) + "\n")
    rows, best = [], float("inf")
    for index, (tag, initial) in enumerate(seeds(base, args.starts)):
        start = time.monotonic()
        c, radius, history = refine(initial, args.iterations)
        row = {"index": index, "seed": tag, "floating_radius": radius,
               "seconds": time.monotonic() - start, "history": history}
        rows.append(row)
        np.save(args.output / f"centers-{index:03d}.npy", c)
        (args.output / f"run-{index:03d}.json").write_text(json.dumps(row, indent=2) + "\n")
        if radius < best:
            best = radius
            np.save(args.output / "best-centers.npy", c)
        print(json.dumps({k: v for k, v in row.items() if k != "history"}), flush=True)
    report = {
        "schema": "N26-moving-voronoi-component-numeric-search-v1", "N": 26,
        "best_floating_radius": best, "continuous_cover_proved": False,
        "global_optimality_proved": False, "calibration": checks,
        "runs": rows, "files": {str(path): sha(path) for path in (
            Path(__file__), Path(__file__).with_name("continuous_cover_search.py"),
            args.base, args.output / "best-centers.npy")},
    }
    (args.output / "REPORT.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"best_floating_radius": best, "starts_completed": len(rows),
                      "continuous_cover_proved": False}), flush=True)


if __name__ == "__main__":
    main()
