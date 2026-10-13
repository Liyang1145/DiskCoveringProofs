"""Exact finite regressions for the cover-specific origin screen.

No assertion here certifies arbitrary continuous geometry. The geometric
argument is bound as a manuscript and remains subject to final interface review.
"""

import argparse
from collections import Counter
from fractions import Fraction as F
from itertools import combinations
import json
from pathlib import Path
import re
import subprocess
import time

from audit_prefix_partition import (
    CAPS, SCALE, WORK, Reference, Runner, check_frontier, native_command, publish, sha,
)


def exposed_by_faces(faces, b):
    boundary = (1 << b) - 1
    exposed = boundary
    for face in faces:
        if face & boundary:
            exposed |= face
    return exposed


class OriginReference(Reference):
    def __init__(self, *args, origin=True, **kwargs):
        super().__init__(*args, **kwargs)
        self.origin = origin

    def possible(self, adjacency):
        if self.origin:
            exposed = (1 << self.b) - 1
            for i in range(self.b):
                exposed |= adjacency[i]
            if exposed == (1 << self.n) - 1:
                return False
        return super().possible(adjacency)


class OriginRunner:
    def __init__(self, folder):
        self.folder = Path(folder)
        self.serial = 0
        self.records = []
        self.binary = WORK / "prefix-origin-v1/peel_prefix_origin.linux"

    def run(self, n, b, mode, origin, operation="solve", prefix=(), depth=0,
            limit=0, allow_failure=False):
        target = self.folder / f"origin-{self.serial:05d}.json"
        logfile = self.folder / f"origin-{self.serial:05d}.log"
        self.serial += 1
        command = native_command(self.binary, [
            str(n), str(b), str(target), str(SCALE), *map(str, CAPS), str(limit),
            mode, operation, ",".join(map(str, prefix)) if prefix else "-", str(depth),
            str(origin),
        ])
        start = time.monotonic()
        result = subprocess.run(command, capture_output=True, timeout=90)
        logfile.write_bytes(result.stdout + result.stderr)
        record = {"path": str(target), "command": command, "exit_code": result.returncode,
                  "log": str(logfile), "log_sha256": sha(logfile),
                  "seconds": time.monotonic() - start}
        if result.returncode:
            if target.exists():
                raise ValueError("failed run published output")
            if not allow_failure:
                raise RuntimeError(logfile.read_text(encoding="utf-8"))
        else:
            record["sha256"] = sha(target)
            record["data"] = json.loads(target.read_text(encoding="utf-8"))
            if record["data"]["origin_screen"] != bool(origin):
                raise ValueError("wrong origin flag in result")
        self.records.append({k: v for k, v in record.items() if k != "data"})
        return record


def validate_disk(n, b, faces):
    if len(faces) != 2 * n - b - 2 or len(set(faces)) != len(faces):
        raise ValueError("bad face number")
    counts = Counter()
    used = set()
    links = [dict() for _ in range(n)]
    for face in faces:
        nodes = [i for i in range(n) if (face >> i) & 1]
        if len(nodes) != 3 or face >= 1 << n:
            raise ValueError("invalid triangle")
        used.update(nodes)
        for u, v in combinations(nodes, 2):
            counts[u, v] += 1
        for v in nodes:
            a, c = [u for u in nodes if u != v]
            links[v].setdefault(a, set()).add(c)
            links[v].setdefault(c, set()).add(a)
    boundary_edges = {tuple(sorted((i, (i + 1) % b))) for i in range(b)}
    if not boundary_edges.issubset(counts) or used != set(range(n)):
        raise ValueError("missing boundary edge or vertex")
    if any(count != (1 if edge in boundary_edges else 2) for edge, count in counts.items()):
        raise ValueError("wrong edge incidence")
    if n - len(counts) + len(faces) != 1:
        raise ValueError("wrong Euler characteristic")
    for v, graph in enumerate(links):
        endpoints = {u for u in graph if len(graph[u]) == 1}
        expected = {(v - 1) % b, (v + 1) % b} if v < b else set()
        if endpoints != expected or any(len(edges) not in (1, 2) for edges in graph.values()):
            raise ValueError("wrong vertex link")
        reached, todo = set(), [next(iter(graph))]
        while todo:
            u = todo.pop()
            if u not in reached:
                reached.add(u)
                todo.extend(graph[u] - reached)
        if reached != set(graph):
            raise ValueError("disconnected link")
    return len(counts)


def exact_irredundancy_counterexample():
    # Four corner centers strictly cover D with radius 3/4:
    # d^2 <= x^2+y^2-|x|-|y|+1/2 <= 1/2 < (3/4)^2.
    sites = [(F(49, 50), F(0)), (F(99, 100), F(0))]
    sites += [(F(x, 2), F(y, 2)) for x in (-1, 1) for y in (-1, 1)]
    points = [(F(99, 101), F(20, 101)), (F(1), F(0)),
              (F(99, 101), F(-20, 101))]
    owners, gaps = [], []
    for point in points:
        if sum(value * value for value in point) != 1:
            raise ValueError("witness not on unit circle")
        ds = [sum((u - v) ** 2 for u, v in zip(point, site)) for site in sites]
        owner = min(range(len(ds)), key=ds.__getitem__)
        if sum(distance == ds[owner] for distance in ds) != 1:
            raise ValueError("owner not strict")
        owners.append(owner)
        gaps.append(str(min(ds[i] - ds[owner] for i in range(len(ds)) if i != owner)))
    if owners != [0, 1, 0] or not F(1, 2) < F(3, 4) ** 2 < 1:
        raise ValueError("counterexample failed")
    d = sites[0][0]
    chord_x = (sites[0][0] + sites[1][0]) / 2
    cap_distance_bound = 1 + d * d - 2 * d * chord_x
    if not cap_distance_bound < F(3, 4) ** 2:
        raise ValueError("nested cap bound failed")
    return {
        "strict_unit_circle_owner_sequence": owners,
        "strict_squared_distance_gaps": gaps,
        "coverage_radius": "3/4",
        "four_corner_cover_squared_distance_upper": "1/2",
        "returning_sites_are_redundant": True,
        "outer_cell_cap_squared_distance_upper": str(cap_distance_bound),
        "scope": "Shows why irredundancy is needed for the qualitative no-return lemma; not a radius-U N26 counterexample.",
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists() or args.report.exists():
        raise FileExistsError("new output required")
    args.output.mkdir(parents=True)
    old = Runner(args.output, WORK / "peel_prefix_v1.linux")
    new = OriginRunner(args.output)
    tests = []
    pairs = [(4, 3), (6, 3), (7, 3), (8, 3), (9, 3), (7, 4), (8, 4), (9, 4)]
    for n, b in pairs:
        for mode in ("noscreen", "audit-noscreen"):
            baseline = old.run(n, b, mode)["data"]
            off = new.run(n, b, mode, 0)["data"]
            if off["survivors"] != baseline["survivors"] or off["rooted"] != baseline["rooted"]:
                raise AssertionError("origin-off changed original enumeration")
            allowed = [
                row for row in baseline["survivors"]
                if exposed_by_faces(row["faces"], b) != (1 << n) - 1
            ]
            expected_rooted = sum(2 * b // row["stabilizer"] for row in allowed)
            on = new.run(n, b, mode, 1)["data"]
            if on["survivors"] != allowed or on["rooted"] != expected_rooted:
                raise AssertionError("early origin pruning differs from complete-graph filter")
            tests.append({
                "N": n, "B": b, "mode": mode,
                "original_orbits": baseline["orbits"], "retained_orbits": on["orbits"],
                "removed_orbits": baseline["orbits"] - on["orbits"],
                "origin_prunes": on["origin_prunes"],
            })
        print(f"PASS exact origin postfilter N={n} B={b}", flush=True)
    if not any(test["retained_orbits"] > 0 and test["removed_orbits"] > 0 for test in tests):
        raise ValueError("regressions do not include both retained and removed graphs")

    frontier_tests = []
    for n, b, depth, mode in ((8, 3, 6, "noscreen"), (8, 3, 6, "audit-noscreen"),
                             (26, 18, 2, "dfs")):
        result = new.run(n, b, mode, 1, "frontier", depth=depth)["data"]
        reference = OriginReference(n, b, mode)
        entries = check_frontier(result, reference, (), depth)
        for row in entries:
            exposed = (1 << b) - 1
            for vertex in range(b):
                exposed |= row["adjacency"][vertex]
            if exposed != exposed_by_faces(row["faces"], b):
                raise AssertionError("adjacency-based and face-based exposure disagree")
        frontier_tests.append({"N": n, "B": b, "mode": mode, "depth": depth,
                               "frontier_states_independently_matched": len(entries)})
        print(f"PASS origin frontier N={n} B={b}: {len(entries)} states", flush=True)

    star_tests = []
    for b in range(14, 19):
        faces = [(1 << 0) | (1 << i) | (1 << (i + 1)) for i in range(1, b - 1)]
        n = b
        while n < 26:
            face = faces.pop((n - b) % len(faces))
            vertices = [i for i in range(n) if (face >> i) & 1]
            for u, v in combinations(vertices, 2):
                faces.append((1 << u) | (1 << v) | (1 << n))
            n += 1
            validate_disk(n, b, faces)
        star_tests.append({"N": n, "B": b, "faces": len(faces),
                           "edges": validate_disk(n, b, faces)})

    benchmark = []
    for flag in (0, 1):
        run = new.run(26, 18, "dfs", flag, limit=200000, allow_failure=True)
        text = Path(run["log"]).read_text(encoding="utf-8")
        if run["exit_code"] != 1 or "REJECTED NODE LIMIT:" not in text:
            raise ValueError("bounded N26 probe was not fail-closed")
        metrics = re.search(r"calls=(\d+) origin_prunes=(\d+) survivors=(\d+)", text)
        if metrics is None or int(metrics[1]) != 200000:
            raise ValueError("missing actual terminal metrics")
        benchmark.append({"origin_screen": bool(flag), "calls": int(metrics[1]),
                          "origin_prunes": int(metrics[2]), "partial_survivors": int(metrics[3]),
                          "seconds": run["seconds"], "exit_code": run["exit_code"],
                          "final_output_exists": Path(run["path"]).exists(),
                          "log_sha256": run["log_sha256"]})
    negatives = []
    bad = new.run(26, 18, "dfs", 2, allow_failure=True)
    if bad["exit_code"] == 0 or "invalid origin flag" not in Path(bad["log"]).read_text():
        raise ValueError("invalid origin flag accepted")
    negatives.append("invalid-origin-flag")
    rejected = new.run(26, 18, "dfs", 1, prefix=(999999,), allow_failure=True)
    if rejected["exit_code"] == 0:
        raise ValueError("invalid prefix accepted")
    negatives.append("invalid-prefix")
    negatives.append("node-limit-no-publication")

    proof = WORK.parent / "outputs/n26-geometric-bridge-v1.md"
    paths = (
        Path(__file__), WORK / "derive_prefix_origin.py",
        WORK / "audit_prefix_partition.py", WORK / "peel_synthesis_n26_cap8_prefix.cpp",
        WORK / "peel_prefix_v1.linux",
        WORK / "prefix-origin-v1/DERIVATION.json",
        WORK / "prefix-origin-v1/peel_prefix_origin.cpp", new.binary, proof,
        WORK.parent / "outputs/n26-scope-budget-v1.json",
    )
    report = {
        "schema": "N26-cover-specific-origin-screen-regressions-v1",
        "finite_implementation_checks_verified": True,
        "written_geometric_argument_bound": True,
        "arbitrary_cover_reduction_accepted": False,
        "N26_complete_catalog": False, "global_optimality_proved": False,
        "exact_postfilter_tests": tests, "independent_frontier_tests": frontier_tests,
        "star_subdivision_topology_tests": star_tests,
        "irredundancy_scope_counterexample": exact_irredundancy_counterexample(),
        "bounded_N26_probes": benchmark,
        "negative_controls_rejected": negatives,
        "files": {str(path): sha(path) for path in paths},
        "native_runs": new.records, "baseline_runs": old.calls,
        "scope": "Finite source/binary tests and manuscript binding, not automatic verification of the continuous no-return/topological proof.",
    }
    publish(args.report, report)
    print(json.dumps({"postfilter_tests": len(tests),
                      "matched_frontiers": frontier_tests,
                      "bounded_N26_probes": benchmark,
                      "global_optimality_proved": False}, indent=2), flush=True)


if __name__ == "__main__":
    main()
