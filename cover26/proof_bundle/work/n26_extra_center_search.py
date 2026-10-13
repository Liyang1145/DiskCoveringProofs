import argparse
import json
import math
from fractions import Fraction
from pathlib import Path

import numpy as np
from scipy.optimize import differential_evolution, minimize


def scalar(text: str) -> float:
    return float(Fraction(text))


def load_centers(path: Path) -> np.ndarray:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if obj["N"] != 25 or len(obj["centers"]) != 25:
        raise ValueError("expected exact n=25 geometry")
    q = math.sqrt(2.0)
    a = math.sqrt(2.0 / 3.0 - q / 3.0)
    out = []
    for point in obj["centers"]:
        out.append([a * (scalar(u) + scalar(v) * q) for u, v in point])
    return np.asarray(out, dtype=float)


def samples() -> np.ndarray:
    rows = []
    boundary = np.linspace(0.0, 2.0 * math.pi, 4000, endpoint=False)
    rows.append(np.column_stack((np.cos(boundary), np.sin(boundary))))
    for j in range(1, 201):
        radius = j / 200.0
        angles = np.linspace(0.0, 2.0 * math.pi, 1000, endpoint=False)
        rows.append(np.column_stack((radius * np.cos(angles), radius * np.sin(angles))))
    return np.concatenate(rows, axis=0)


def nearest_distances(centers: np.ndarray, points: np.ndarray) -> np.ndarray:
    best = np.full(len(points), np.inf)
    for i in range(0, len(points), 20000):
        chunk = points[i : i + 20000]
        d2 = ((chunk[:, None, :] - centers[None, :, :]) ** 2).sum(axis=2)
        best[i : i + len(chunk)] = np.sqrt(d2.min(axis=1))
    return best


def objective(extra: np.ndarray, base: np.ndarray, points: np.ndarray) -> float:
    centers = np.vstack((base, np.asarray(extra, dtype=float)))
    return float(nearest_distances(centers, points).max())


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--geometry", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    base = load_centers(args.geometry)
    pts = samples()
    base_dist = nearest_distances(base, pts)
    witness_index = int(base_dist.argmax())
    witness = pts[witness_index]
    bounds = [(-1.1, 1.1), (-1.1, 1.1)]
    de = differential_evolution(
        lambda x: objective(x, base, pts),
        bounds,
        seed=2626,
        maxiter=100,
        popsize=20,
        polish=True,
        workers=1,
        updating="immediate",
    )
    polished = minimize(
        lambda x: objective(x, base, pts),
        de.x,
        method="Nelder-Mead",
        options={"maxiter": 3000, "xatol": 1e-11, "fatol": 1e-11},
    )
    candidate = np.vstack((base, polished.x))
    candidate_dist = nearest_distances(candidate, pts)
    args.output.mkdir(parents=True)
    np.save(args.output / "base_centers.npy", base)
    np.save(args.output / "centers.npy", candidate)
    report = {
        "schema": "N26-add-one-center-to-exact-n25-numeric-search-v1",
        "N": 26,
        "verified": False,
        "continuous_cover_proved": False,
        "global_optimality_proved": False,
        "sample_count": int(len(pts)),
        "n25_sampled_radius": float(base_dist.max()),
        "n25_sampled_worst_point": [float(v) for v in witness],
        "extra_center_initialization": [float(v) for v in witness],
        "extra_center_optimized": [float(v) for v in polished.x],
        "n26_sampled_radius": float(candidate_dist.max()),
        "n26_sampled_worst_point": [float(v) for v in pts[int(candidate_dist.argmax())]],
        "optimizer_success": bool(polished.success),
        "optimizer_message": str(polished.message),
    }
    (args.output / "REPORT.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2), flush=True)


if __name__ == "__main__":
    main()
