import argparse
import json
from pathlib import Path

import numpy as np
from scipy.optimize import minimize


def nearest(centers: np.ndarray, points: np.ndarray):
    best = np.full(len(points), np.inf)
    owner = np.zeros(len(points), dtype=np.int64)
    for i in range(0, len(points), 20000):
        chunk = points[i : i + 20000]
        d2 = ((chunk[:, None, :] - centers[None, :, :]) ** 2).sum(axis=2)
        own = d2.argmin(axis=1)
        vals = np.sqrt(d2[np.arange(len(chunk)), own])
        best[i : i + len(chunk)] = vals
        owner[i : i + len(chunk)] = own
    return best, owner


def objective(z: np.ndarray) -> float:
    return float(z[-1])


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--centers", type=Path, required=True)
    parser.add_argument("--points", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    centers = np.load(args.centers).astype(float)
    points = np.load(args.points).astype(float)
    if centers.shape != (26, 2):
        raise ValueError(centers.shape)
    distances, owners = nearest(centers, points)
    active = set(np.argsort(distances)[-700:].tolist())
    history = []
    z = np.concatenate((centers.reshape(-1), [float(distances.max()) + 1e-6]))
    for iteration in range(8):
        ids = np.array(sorted(active), dtype=np.int64)
        active_points = points[ids]
        active_owners = owners[ids]

        def constraints(x):
            c = x[:-1].reshape(26, 2)
            r = x[-1]
            delta = active_points - c[active_owners]
            return r * r - (delta * delta).sum(axis=1)

        result = minimize(
            objective,
            z,
            method="SLSQP",
            constraints={"type": "ineq", "fun": constraints},
            bounds=[(-1.2, 1.2)] * 52 + [(0.0, 1.0)],
            options={"maxiter": 250, "ftol": 1e-11, "disp": False},
        )
        z = result.x
        centers = z[:-1].reshape(26, 2)
        distances, owners = nearest(centers, points)
        worst = int(distances.argmax())
        top = np.argsort(distances)[-700:]
        active.update(int(i) for i in top)
        history.append(
            {
                "iteration": iteration,
                "success": bool(result.success),
                "message": str(result.message),
                "active_count": len(active),
                "sampled_radius": float(distances.max()),
                "worst_point": [float(v) for v in points[worst]],
            }
        )
        print(json.dumps(history[-1]), flush=True)
    args.output.mkdir(parents=True)
    np.save(args.output / "centers.npy", centers)
    report = {
        "schema": "N26-active-set-local-refinement-v1",
        "N": 26,
        "sample_count": int(len(points)),
        "verified": False,
        "continuous_cover_proved": False,
        "global_optimality_proved": False,
        "sampled_radius": float(distances.max()),
        "worst_point": [float(v) for v in points[int(distances.argmax())]],
        "history": history,
    }
    (args.output / "REPORT.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2), flush=True)


if __name__ == "__main__":
    main()
