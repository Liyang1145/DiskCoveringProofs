import argparse
import json
import math
from pathlib import Path

import numpy as np
from scipy.optimize import differential_evolution, minimize


def sample() -> np.ndarray:
    rows = []
    boundary = np.linspace(0.0, 2.0 * math.pi, 2400, endpoint=False)
    rows.append(np.column_stack((np.cos(boundary), np.sin(boundary))))
    for j in range(1, 61):
        radius = j / 60.0
        count = 720
        angles = np.linspace(0.0, 2.0 * math.pi, count, endpoint=False)
        rows.append(np.column_stack((radius * np.cos(angles), radius * np.sin(angles))))
    return np.concatenate(rows, axis=0)


def centers(x: np.ndarray, counts: tuple[int, ...], with_origin: bool) -> np.ndarray:
    out = []
    k = 0
    if with_origin:
        out.append((0.0, 0.0))
    for ring_index, count in enumerate(counts):
        radius = x[k]
        phase = x[k + 1]
        k += 2
        for j in range(count):
            angle = phase + 2.0 * math.pi * j / count
            out.append((radius * math.cos(angle), radius * math.sin(angle)))
    return np.asarray(out, dtype=float)


def radius(x: np.ndarray, points: np.ndarray, counts: tuple[int, ...], with_origin: bool) -> float:
    c = centers(x, counts, with_origin)
    best = 0.0
    for i in range(0, len(points), 20000):
        chunk = points[i : i + 20000]
        d2 = ((chunk[:, None, :] - c[None, :, :]) ** 2).sum(axis=2)
        best = max(best, float(np.sqrt(d2.min(axis=1).max())))
    return best


def run_family(points: np.ndarray, counts: tuple[int, ...], with_origin: bool, seed: int):
    bounds = []
    for _ in counts:
        bounds.append((0.15, 1.1))
        bounds.append((-math.pi / max(counts), math.pi / max(counts)))
    result = differential_evolution(
        lambda x: radius(x, points, counts, with_origin),
        bounds,
        maxiter=60,
        popsize=12,
        seed=seed,
        polish=False,
        workers=1,
        updating="immediate",
    )
    polished = minimize(
        lambda x: radius(x, points, counts, with_origin),
        result.x,
        method="Nelder-Mead",
        options={"maxiter": 3500, "xatol": 1e-10, "fatol": 1e-10},
    )
    return {
        "counts": list(counts),
        "with_origin": with_origin,
        "sampled_radius": radius(polished.x, points, counts, with_origin),
        "parameters": [float(v) for v in polished.x],
        "success": bool(polished.success),
        "message": str(polished.message),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    assert not args.output.exists()
    points = sample()
    families = [
        ((8, 9, 9), False),
        ((7, 9, 10), False),
        ((8, 8, 10), False),
    ]
    results = []
    for idx, (counts, with_origin) in enumerate(families):
        results.append(run_family(points, counts, with_origin, 2600 + idx))
        print(json.dumps(results[-1]), flush=True)
    args.output.mkdir(parents=True)
    report = {
        "schema": "N26-generic-ring-family-probe-v1",
        "N": 26,
        "sample_count": int(len(points)),
        "verified": False,
        "continuous_cover_proved": False,
        "global_optimality_proved": False,
        "families": results,
    }
    (args.output / "REPORT.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2), flush=True)


if __name__ == "__main__":
    main()
