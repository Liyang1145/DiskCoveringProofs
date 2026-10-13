import argparse
import json
import math
from itertools import combinations
from pathlib import Path

import numpy as np


def nearest(centers: np.ndarray, points: np.ndarray) -> np.ndarray:
    out = np.empty(len(points), dtype=float)
    for i in range(0, len(points), 20000):
        chunk = points[i : i + 20000]
        d2 = ((chunk[:, None, :] - centers[None, :, :]) ** 2).sum(axis=2)
        out[i : i + len(chunk)] = np.sqrt(d2.min(axis=1))
    return out


def candidates(centers: np.ndarray) -> np.ndarray:
    rows = [(0.0, 0.0)]
    for c in centers:
        norm = float(np.linalg.norm(c))
        if norm > 1e-14:
            rows.append((c / norm).tolist())
            rows.append((-c / norm).tolist())
    for i, j in combinations(range(len(centers)), 2):
        ci, cj = centers[i], centers[j]
        n = cj - ci
        nn = float(np.dot(n, n))
        if nn < 1e-20:
            continue
        h = (float(np.dot(cj, cj)) - float(np.dot(ci, ci))) / 2.0
        q = h * h / nn
        if q > 1.0 + 1e-12:
            continue
        p0 = (h / nn) * n
        t = math.sqrt(max(0.0, 1.0 - q))
        perp = np.array([-n[1], n[0]]) / math.sqrt(nn)
        rows.append((p0 + t * perp).tolist())
        rows.append((p0 - t * perp).tolist())
    for i, j, k in combinations(range(len(centers)), 3):
        ci, cj, ck = centers[i], centers[j], centers[k]
        A = 2.0 * np.vstack((cj - ci, ck - ci))
        b = np.array(
            [
                float(np.dot(cj, cj) - np.dot(ci, ci)),
                float(np.dot(ck, ck) - np.dot(ci, ci)),
            ]
        )
        det = float(np.linalg.det(A))
        if abs(det) < 1e-12:
            continue
        v = np.linalg.solve(A, b)
        if float(np.dot(v, v)) <= 1.0 + 1e-12:
            rows.append(v.tolist())
    return np.unique(np.asarray(rows, dtype=float).round(14), axis=0)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--centers", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    centers = np.load(args.centers).astype(float)
    pts = candidates(centers)
    distances = nearest(centers, pts)
    idx = int(distances.argmax())
    report = {
        "schema": "N26-floating-voronoi-boundary-audit-v1",
        "N": 26,
        "candidate_count": int(len(pts)),
        "interior_or_boundary_vertex_audit": True,
        "sampled_max_distance": float(distances[idx]),
        "worst_point": [float(v) for v in pts[idx]],
        "verified": False,
        "continuous_cover_proved": False,
        "global_optimality_proved": False,
        "warning": "Floating-point geometric audit only; no exact interval or theorem.",
    }
    args.output.mkdir(parents=True)
    (args.output / "REPORT.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    np.save(args.output / "candidate_points.npy", pts)
    print(json.dumps(report, indent=2), flush=True)


if __name__ == "__main__":
    main()
