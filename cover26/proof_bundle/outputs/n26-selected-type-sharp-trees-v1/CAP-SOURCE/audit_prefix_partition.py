"""Partition regression and independent integer frontier reconstruction.

This audits the combinatorial implementation, not the arbitrary-cover theorem.
Native and Python code share the stated mathematical recurrence, but the Python
screen uses BFS distances rather than bitset closure. Completed subtrees are
merged by canonical graph union, NOT by adding orbit counts.
"""

import argparse
from collections import deque
from copy import deepcopy
from dataclasses import dataclass
from functools import lru_cache
import hashlib
import json
from math import comb, factorial
from pathlib import Path
import subprocess
import sys
import time


WORK = Path(__file__).resolve().parent
CAPS = (768677, 1587443, 2546859, 4058615)
SCALE = 10**7


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def linux(path):
    path = Path(path).resolve()
    text = path.as_posix()
    if text.startswith("/"):
        return text
    if len(text) < 3 or text[1:3] != ":/":
        raise ValueError(path)
    return "/mnt/" + text[0].lower() + text[2:]


def native_command(binary, arguments):
    command = ["/lib64/ld-linux-x86-64.so.2", linux(binary), *arguments]
    return ["wsl.exe", "--", *command] if sys.platform == "win32" else command


def publish(path, data):
    if Path(path).exists():
        raise FileExistsError(path)
    Path(path).write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")


@dataclass(frozen=True)
class State:
    adjacency: tuple
    faces: tuple
    next_vertex: int
    pending: tuple


class Reference:
    def __init__(self, n, b, mode, caps=CAPS, scale=SCALE):
        self.n, self.b = n, b
        self.mode = mode
        self.audit = mode.startswith("audit")
        self.screen = "noscreen" not in mode
        self.caps, self.scale = tuple(caps), scale
        self.screen_cache = {}

    def initial(self):
        adjacency = [0] * self.n
        for i in range(self.b):
            j = (i + 1) % self.b
            adjacency[i] |= 1 << j
            adjacency[j] |= 1 << i
        boundary = tuple(range(self.b))
        if self.audit:
            k = self.b // 2
            boundary = boundary[k:] + boundary[:k]
        return State(tuple(adjacency), (), self.b, ((boundary, self.n - self.b),))

    def pick(self, pending):
        chosen = len(pending) - 1
        if self.audit:
            for i in range(len(pending)):
                if (pending[i][1] < pending[chosen][1]
                    or (pending[i][1] == pending[chosen][1]
                        and len(pending[i][0]) > len(pending[chosen][0]))):
                    chosen = i
        return chosen

    def normalize(self, state):
        pending = list(state.pending)
        while pending:
            pick = self.pick(pending)
            boundary, inside = pending[pick]
            if len(boundary) != 2:
                break
            if inside:
                raise ValueError("nonempty digon")
            pending.pop(pick)
        return State(state.adjacency, state.faces, state.next_vertex, tuple(pending))

    def possible(self, adjacency):
        if not self.screen:
            return True
        if adjacency in self.screen_cache:
            return self.screen_cache[adjacency]
        neighbors = [
            [j for j in range(self.n) if (mask >> j) & 1] for mask in adjacency
        ]
        # Independent shortest-path BFS: capped distance 3 is all the screen uses.
        distances = []
        for start in range(self.b):
            ds = [self.n + 1] * self.n
            ds[start] = 0
            queue = deque([start])
            while queue:
                u = queue.popleft()
                if ds[u] == 3:
                    continue
                for v in neighbors[u]:
                    if ds[v] > ds[u] + 1:
                        ds[v] = ds[u] + 1
                        queue.append(v)
            distances.append(ds)
        edges = []
        for i in range(self.b):
            j = (i + 1) % self.b
            edges += [(i, j, self.caps[0] - (self.scale if j == 0 else 0)),
                      (j, i, self.scale if j == 0 else 0)]
        valid = True
        for i in range(self.b):
            for j in range(i + 1, self.b):
                graph_distance = min(
                    distances[u][v]
                    for u in (i, (i + 1) % self.b)
                    for v in (j, (j + 1) % self.b)
                )
                if graph_distance > 3:
                    continue
                cap = self.caps[max(1, graph_distance)]
                k = j - i
                if min(k, self.b - k) * self.caps[0] <= cap:
                    continue
                forward = k * self.caps[0] < self.scale - cap
                backward = (self.b - k) * self.caps[0] < self.scale - cap
                if forward and backward:
                    valid = False
                    break
                if forward:
                    edges.append((i, j, cap))
                elif backward:
                    edges.append((j, i, cap - self.scale))
            if not valid:
                break
        if valid:
            dist = [0] * self.b
            for _ in range(self.b):
                changed = False
                for u, v, w in edges:
                    if dist[v] > dist[u] + w:
                        dist[v] = dist[u] + w
                        changed = True
                if not changed:
                    break
            else:
                valid = False
        self.screen_cache[adjacency] = valid
        return valid

    def children(self, state):
        state = self.normalize(state)
        if not state.pending:
            return []
        pending = list(state.pending)
        boundary, inside = pending.pop(self.pick(pending))
        size = len(boundary)
        a, c = boundary[:2]
        result = []
        choices = range(size - 1, 1, -1) if self.audit else range(2, size)
        for k in choices:
            w = boundary[k]
            if k > 2 and (state.adjacency[c] >> w) & 1:
                continue
            if k < size - 1 and (state.adjacency[a] >> w) & 1:
                continue
            adjacency = list(state.adjacency)
            changed = False
            for u, v in ((a, w), (c, w)):
                changed |= not ((adjacency[u] >> v) & 1)
                adjacency[u] |= 1 << v
                adjacency[v] |= 1 << u
            adjacency = tuple(adjacency)
            if changed and not self.possible(adjacency):
                continue
            faces = state.faces + ((1 << a) | (1 << c) | (1 << w),)
            left, right = (w,) + boundary[1:k], (a,) + boundary[k:]
            splits = range(inside, -1, -1) if self.audit else range(inside + 1)
            for left_inside in splits:
                if ((len(left) == 2 and left_inside)
                    or (len(right) == 2 and inside - left_inside)):
                    continue
                new_regions = (
                    ((left, left_inside), (right, inside - left_inside))
                    if self.audit else
                    ((right, inside - left_inside), (left, left_inside))
                )
                result.append(State(adjacency, faces, state.next_vertex,
                                    tuple(pending) + new_regions))
        if inside:
            v = state.next_vertex
            adjacency = list(state.adjacency)
            for u in (a, c):
                adjacency[v] |= 1 << u
                adjacency[u] |= 1 << v
            adjacency = tuple(adjacency)
            if self.possible(adjacency):
                faces = state.faces + ((1 << a) | (1 << c) | (1 << v),)
                polygon = (a, v) + boundary[1:]
                result.append(State(adjacency, faces, v + 1,
                                    tuple(pending) + ((polygon, inside - 1),)))
        return result

    def resolve(self, prefix):
        state = self.initial()
        if not self.possible(state.adjacency):
            if prefix:
                raise ValueError("prefix under rejected root")
            return None
        for k in prefix:
            if type(k) is not int or k < 0:
                raise ValueError("bad prefix")
            kids = self.children(state)
            if k >= len(kids):
                raise ValueError("prefix outside child range")
            state = kids[k]
        return self.normalize(state)

    def entry(self, prefix, state, kids):
        return {
            "prefix": list(prefix), "terminal": not state.pending,
            "child_count": len(kids), "next": state.next_vertex,
            "faces": list(state.faces), "adjacency": list(state.adjacency),
            "pending": [{"boundary": list(boundary), "interior": inside}
                        for boundary, inside in state.pending],
        }

    def frontier(self, prefix, depth):
        initial = self.resolve(prefix)
        result = []

        def walk(path, state, remaining):
            state = self.normalize(state)
            kids = self.children(state)
            if not remaining or not state.pending or not kids:
                result.append(self.entry(path, state, kids))
                return
            for k, child in enumerate(kids):
                walk(path + (k,), child, remaining - 1)
        if initial is not None:
            walk(tuple(prefix), initial, depth)
        return result


@lru_cache(None)
def labelled(b, i):
    if b == 2:
        return int(i == 0)
    value = sum(comb(i, j) * labelled(k, j) * labelled(b - k + 1, i - j)
                for k in range(2, b) for j in range(i + 1))
    if i:
        value += i * (labelled(b + 1, i - 1)
                      - sum(comb(i - 1, j) * labelled(3, j) * labelled(b, i - 1 - j)
                            for j in range(i)))
    return value


def check_frontier(data, reference, prefix, depth):
    if not (data["complete"] and data["operation"] == "frontier"
            and data["N"] == reference.n and data["B"] == reference.b
            and data["scale"] == reference.scale and data["caps"] == list(reference.caps)
            and data["prefix"] == list(prefix) and data["frontier_depth"] == depth
            and data["mode"] == reference.mode
            and data["screen"] == reference.screen
            and data["family_complete"] is False
            and data["geometric_reduction_proved"] is False
            and data["global_optimality_proved"] is False):
        raise ValueError("frontier metadata mismatch")
    expected = reference.frontier(tuple(prefix), depth)
    if data["frontier"] != expected:
        raise ValueError("frontier omits, duplicates, or changes a generated state")
    return expected


def merge_parts(frontier, records, n, b, mode, caps=CAPS, scale=SCALE):
    expected = {tuple(row["prefix"]) for row in frontier}
    if len(expected) != len(frontier) or len(records) != len(expected):
        raise ValueError("incomplete or duplicate partition")
    graphs, seen, rooted = {}, set(), 0
    for record in records:
        data = record["data"]
        path = tuple(data["prefix"])
        if record["exit_code"] != 0 or path not in expected or path in seen:
            raise ValueError("failed, unexpected, or duplicate subtree")
        if sha(record["path"]) != record["sha256"]:
            raise ValueError("changed subtree content")
        if json.loads(Path(record["path"]).read_text(encoding="utf-8")) != data:
            raise ValueError("record differs from bound file")
        if not (data["complete"] and data["operation"] == "solve"
                and data["N"] == n and data["B"] == b and data["mode"] == mode
                and data["caps"] == list(caps) and data["scale"] == scale
                and data["family_complete"] == (len(path) == 0)
                and data["geometric_reduction_proved"] is False
                and data["global_optimality_proved"] is False):
            raise ValueError("wrong subtree metadata")
        seen.add(path)
        rooted += data["rooted"]
        local_seen = set()
        for graph in data["survivors"]:
            code, stabilizer = tuple(graph["faces"]), graph["stabilizer"]
            if code in local_seen or (code in graphs and graphs[code] != stabilizer):
                raise ValueError("duplicate graph or inconsistent stabilizer")
            local_seen.add(code)
            graphs[code] = stabilizer
        if data["orbits"] != len(local_seen):
            raise ValueError("wrong orbit count")
    if seen != expected:
        raise ValueError("partition not exhausted")
    return {"rooted": rooted, "orbits": len(graphs),
            "survivors": [{"faces": list(code), "stabilizer": graphs[code]}
                          for code in sorted(graphs)]}


class Runner:
    def __init__(self, output, binary):
        self.output, self.binary = Path(output), Path(binary)
        self.calls = []
        self.serial = 0

    def run(self, n, b, mode, operation="solve", prefix=(), depth=0, limit=0,
            caps=CAPS, scale=SCALE, allow_failure=False, raw_prefix=None):
        index = self.serial
        self.serial += 1
        target = self.output / f"run-{index:05d}.json"
        logfile = self.output / f"run-{index:05d}.log"
        p = raw_prefix if raw_prefix is not None else (
            ",".join(map(str, prefix)) if prefix else "-"
        )
        command = native_command(self.binary, [
            str(n), str(b), linux(target), str(scale), *map(str, caps),
            str(limit), mode, operation, p, str(depth)])
        start = time.monotonic()
        run = subprocess.run(command, capture_output=True, timeout=90)
        logfile.write_bytes(run.stdout + run.stderr)
        rec = {"path": str(target), "log": str(logfile),
               "log_sha256": sha(logfile), "command": command,
               "exit_code": run.returncode, "seconds": time.monotonic() - start}
        if run.returncode:
            if target.exists():
                raise ValueError("failed run published final output")
            if not allow_failure:
                raise RuntimeError(logfile.read_text(encoding="utf-8", errors="replace"))
        else:
            rec["sha256"] = sha(target)
            rec["data"] = json.loads(target.read_text(encoding="utf-8"))
        self.calls.append({k: v for k, v in rec.items() if k != "data"})
        return rec


def expect_rejection(name, call, negatives):
    try:
        call()
    except (ValueError, KeyError, AssertionError):
        negatives.append(name)
        return
    raise AssertionError("negative control accepted: " + name)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    args.output.mkdir(parents=True)
    binary = WORK / "peel_prefix_v1.linux"
    original = WORK / "peel_synthesis_n26_cap8.exe"
    runner = Runner(args.output, binary)
    tests, negatives = [], []
    # Compare full named subtrees and their unions to the unpartitioned kernel.
    pairs = [(3, 0), (3, 1), (3, 2), (3, 3), (4, 1), (4, 2), (5, 1), (6, 0)]
    for b, inside in pairs:
        n = b + inside
        full_results = []
        for mode in ("noscreen", "audit-noscreen"):
            root = runner.run(n, b, mode)["data"]
            reference = Reference(n, b, mode)
            frontier_record = runner.run(n, b, mode, "frontier", depth=2)
            frontier = check_frontier(frontier_record["data"], reference, (), 2)
            parts = [runner.run(n, b, mode, prefix=row["prefix"]) for row in frontier]
            merged = merge_parts(frontier, parts, n, b, mode)
            if merged["survivors"] != root["survivors"] or merged["rooted"] != root["rooted"]:
                raise AssertionError("subtree union differs from unpartitioned solve")
            total = labelled(b, inside)
            if root["rooted"] * factorial(inside) != total:
                raise AssertionError("labelled recurrence mismatch")
            if sum(2 * b * factorial(inside) // row["stabilizer"]
                   for row in root["survivors"]) != total:
                raise AssertionError("orbit-stabilizer mass mismatch")
            # Existing C++ kernel is retained as a before-refactor oracle.
            target = args.output / f"original-N{n}-B{b}-{mode}.json"
            command = native_command(original, [
                str(n), str(b), linux(target), str(SCALE), *map(str, CAPS), "0", mode])
            result = subprocess.run(command, capture_output=True, timeout=90)
            publish(args.output / f"original-N{n}-B{b}-{mode}-launch.json",
                    {"command": command, "exit_code": result.returncode,
                     "stdout": result.stdout.decode("utf-8", errors="replace"),
                     "stderr": result.stderr.decode("utf-8", errors="replace")})
            if result.returncode:
                raise AssertionError("baseline failed")
            baseline = json.loads(target.read_text())
            if baseline["survivors"] != root["survivors"] or baseline["rooted"] != root["rooted"]:
                raise AssertionError("refactor changed baseline enumeration")
            tests.append({"N": n, "B": b, "mode": mode, "prefix_depth": 2,
                          "parts": len(parts), "rooted": root["rooted"],
                          "orbits": root["orbits"], "labelled": total,
                          "baseline_sha256": sha(target),
                          "frontier_sha256": frontier_record["sha256"]})
            full_results.append(root["survivors"])
        if full_results[0] != full_results[1]:
            raise AssertionError("DFS/audit survivor sets differ")
        print(f"PASS census/union B={b} I={inside}", flush=True)

    # Nontrivial screened families use a wide synthetic angle budget solely for
    # implementation regression. These are NOT N26 geometric constants.
    synthetic = (180000, 370000, 460000, 490000)
    for mode in ("dfs", "audit"):
        reference = Reference(8, 6, mode, synthetic, 10**6)
        root = runner.run(8, 6, mode, caps=synthetic, scale=10**6)["data"]
        rec = runner.run(8, 6, mode, "frontier", depth=3, caps=synthetic, scale=10**6)
        frontier = check_frontier(rec["data"], reference, (), 3)
        parts = [runner.run(8, 6, mode, prefix=row["prefix"], caps=synthetic, scale=10**6)
                 for row in frontier]
        merged = merge_parts(frontier, parts, 8, 6, mode, synthetic, 10**6)
        if merged["survivors"] != root["survivors"] or merged["rooted"] != root["rooted"]:
            raise AssertionError("screened partition mismatch")
        tests.append({"N": 8, "B": 6, "mode": mode, "synthetic_budget": True,
                      "parts": len(parts), "rooted": root["rooted"], "orbits": root["orbits"]})
        print(f"PASS synthetic screened union {mode}: {len(parts)} parts", flush=True)

    # Real N26 root and recursive frontier, independently reconstructed.
    actual = runner.run(26, 18, "dfs", "frontier", depth=2)
    actual_ref = Reference(26, 18, "dfs")
    actual_frontier = check_frontier(actual["data"], actual_ref, (), 2)
    root_children = actual_ref.children(actual_ref.initial())
    counts = {k: 0 for k in range(len(root_children))}
    for row in actual_frontier:
        counts[row["prefix"][0]] += 1
    tests.append({"N": 26, "B": 18, "mode": "dfs",
                  "root_children": len(root_children), "depth2_parts": len(actual_frontier),
                  "frontier_sha256": actual["sha256"], "per_root_counts": counts})
    print(f"PASS N26 B18 frontier: {len(root_children)} roots, {len(actual_frontier)} depth2 parts", flush=True)

    for label, mutate in [
        ("omitted-frontier-child", lambda d: d["frontier"].pop()),
        ("duplicate-frontier-child", lambda d: d["frontier"].append(d["frontier"][0])),
        ("changed-child-index", lambda d: d["frontier"][0]["prefix"].__setitem__(0, 999999)),
        ("changed-state-adjacency", lambda d: d["frontier"][0]["adjacency"].__setitem__(0, 0)),
        ("wrong-N", lambda d: d.__setitem__("N", 25)),
        ("wrong-cap8", lambda d: d["caps"].__setitem__(3, 4058614)),
        ("subtree-claimed-as-family", lambda d: d.__setitem__("family_complete", True)),
    ]:
        wrong = deepcopy(actual["data"])
        mutate(wrong)
        expect_rejection(label, lambda: check_frontier(wrong, actual_ref, (), 2), negatives)

    for label, kwargs in [
        ("node-limit-no-publication", {"limit": 1, "prefix": (0,)}),
        ("out-of-range-prefix", {"raw_prefix": "999999"}),
        ("negative-prefix", {"raw_prefix": "-1"}),
        ("malformed-prefix", {"raw_prefix": "0,"}),
        ("wrong-mode", {"mode": "wrong-mode"}),
        ("negative-limit", {"limit": -1}),
        ("solve-with-depth", {"depth": 1}),
    ]:
        values = {"n": 26, "b": 18, "mode": "dfs", "allow_failure": True}
        values.update(kwargs)
        rec = runner.run(**values)
        if rec["exit_code"] == 0:
            raise AssertionError("invalid invocation accepted")
        negatives.append(label)
    # Subtree merge must refuse a missing, duplicate, or failed completed task.
    small_frontier_rec = runner.run(6, 4, "noscreen", "frontier", depth=1)
    small_frontier = check_frontier(small_frontier_rec["data"], Reference(6, 4, "noscreen"), (), 1)
    parts = [runner.run(6, 4, "noscreen", prefix=r["prefix"]) for r in small_frontier]
    expect_rejection("missing-subtree-result",
                     lambda: merge_parts(small_frontier, parts[:-1], 6, 4, "noscreen"), negatives)
    expect_rejection("duplicate-subtree-result",
                     lambda: merge_parts(small_frontier, parts[:-1] + parts[:1], 6, 4, "noscreen"), negatives)
    wrong_parts = deepcopy(parts)
    wrong_parts[0]["exit_code"] = 1
    expect_rejection("nonzero-exit-result",
                     lambda: merge_parts(small_frontier, wrong_parts, 6, 4, "noscreen"), negatives)
    wrong_parts = deepcopy(parts)
    wrong_parts[0]["sha256"] = "0" * 64
    expect_rejection("changed-content-binding",
                     lambda: merge_parts(small_frontier, wrong_parts, 6, 4, "noscreen"), negatives)
    report = {
        "schema": "N26-recursive-prefix-partition-regressions-v1",
        "verified_implementation_tests": True,
        "N26_complete_catalog": False,
        "arbitrary_cover_reduction_proved": False,
        "global_optimality_proved": False,
        "tests": tests, "negative_controls_rejected": negatives,
        "files": {str(p): sha(p) for p in (
            Path(__file__), WORK / "peel_synthesis_n26_cap8_prefix.cpp",
            binary, WORK / "peel_synthesis_n26_cap8.cpp", original)},
        "runs": runner.calls,
        "scope": "Exact combinatorial partition and finite census implementation checks; no geometric proof.",
    }
    publish(args.output / "VERIFIED.json", report)
    print(json.dumps({"passed_tests": len(tests), "negative_controls": len(negatives),
                      "N26_B18_root_children": len(root_children),
                      "N26_B18_depth2_parts": len(actual_frontier)}), flush=True)


if __name__ == "__main__":
    main()
