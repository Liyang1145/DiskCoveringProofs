"""Floating proposal only for a rigorous Voronoi degree/arc area dual."""

from collections import Counter
import json
from math import asin, pi
from pathlib import Path
import numpy as np

from new_upper_scope import local_path


WORK = Path(__file__).resolve().parent
OUT = WORK.parent / "outputs"


def catalogs():
    result = {}
    for b in (14, 15, 16, 17):
        report = json.loads((OUT / f"n26-new-B{b}-progress-v1.json").read_text())
        manifest = json.loads(local_path(report["latest_checkpoint"]).read_text())
        for event in manifest["events"]:
            if event["kind"] == "closed":
                data = json.loads(local_path(event["run"]["path"]).read_text())
                for graph in data["survivors"]:
                    result[b, tuple(graph["faces"])] = graph
    return result


def profile(b, faces):
    adjacency = [set() for _ in range(26)]
    for face in faces:
        vertices = [i for i in range(26) if face >> i & 1]
        for i in vertices:
            adjacency[i].update(v for v in vertices if v != i)
    boundary = Counter(len(adjacency[i]) for i in range(b))
    interior = Counter(len(adjacency[i]) for i in range(b, 26))
    return tuple(boundary[k] for k in range(2, 26)), tuple(interior[k] for k in range(2, 26))


def main():
    counts = Counter(profile(b, faces) for b, faces in catalogs())
    U = 234701 / 10**6
    t = U * U
    x = np.linspace(0, asin(U) / pi, 8193)
    rows = []
    beta = np.arcsin(np.minimum(1, np.sin(pi * x) / U))
    for d in range(2, 26):
        a = .5 * t * (d + 1) * np.sin(2 * pi / (d + 1))
        active = (2 * np.sin(pi * x) > U) & (beta >= pi / (d + 1))
        special = .5 * t * (np.sin(2 * beta) + d * np.sin((2 * pi - 2 * beta) / d))
        rows.append(np.where(active, special, a) - .5 * np.sin(2 * pi * x))
    h = np.array(rows)
    profiles = list(counts)
    bd = np.array([p[0] for p in profiles])
    interior_coefficients = np.array([.5 * t * d * np.sin(2 * pi / d) for d in range(2, 26)])
    interiors = np.array([p[1] for p in profiles]) @ interior_coefficients
    best = np.full(len(profiles), np.inf)
    chosen = np.zeros(len(profiles), dtype=int)
    for q in range(-160, 1):
        slope = q / 4
        intercept = np.max(h - slope * x[None, :], axis=1)
        value = interiors + bd @ intercept + slope
        improve = value < best
        best[improve] = value[improve]
        chosen[improve] = q
    proposals = [
        {"boundary_degree_counts": list(p[0]), "interior_degree_counts": list(p[1]),
         "graph_count": counts[p], "slope_quarters": int(chosen[i]),
         "floating_area_dual_upper_proposal": float(best[i])}
        for i, p in enumerate(profiles)]
    path = WORK / "n26-degree-area-proposals-v1.json"
    if path.exists():
        raise FileExistsError(path)
    path.write_text(json.dumps({"verified": False, "proposals": proposals,
                                "local_optimality_proved": False,
                                "global_optimality_proved": False}, indent=2) + "\n")
    print(json.dumps({"verified": False, "profiles": len(profiles),
                      "graphs": sum(counts.values()),
                      "proposed_excluded_profiles": int(np.sum(best < 0)),
                      "proposed_excluded_graphs": sum(counts[p] for i, p in enumerate(profiles) if best[i] < 0),
                      "minimum_dual_upper": float(best.min()), "maximum_dual_upper": float(best.max()),
                      "slopes_quarters": sorted(set(int(q) for q in chosen))}), flush=True)


if __name__ == "__main__":
    main()
