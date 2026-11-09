"""Find reusable b=14 flow proofs, checkpointed after each belt."""

import argparse
import json
import os
import time
from collections import defaultdict, deque
from multiprocessing import get_context
from pathlib import Path

os.environ["OMP_NUM_THREADS"] = "1"
os.environ["OPENBLAS_NUM_THREADS"] = "1"

from find_belt_geometry import free_angle_flow, graph_flow, search
from linear_flow14 import linear_angle_flow
from verify_belt_geometry import build_graph, starting_constraints
from verify_belt_pruning import B, cut_table, parse_belt
from verify_fills14 import INSIDE, origin_radius, parse_fill
from verify_patch14 import RADIUS
from verify_transfer14 import check_proof, face_mask, shell_mask


def init(cuts_file):
    global CUTS
    CUTS = cut_table(json.loads(Path(cuts_file).read_text(encoding="utf-8")))


def sparse_flow(flow, free, edges):
    """Drop negligible edges, then route integer imbalance on the retained graph."""
    size = max(abs(x) + abs(y) for x, y in flow)
    vertices = max(max(e) for e in edges) + 1
    incident = [[] for _ in range(vertices)]
    kept = [False] * len(edges)
    for i, ((u, v), (x, y)) in enumerate(zip(edges, flow)):
        if 10000 * (abs(x) + abs(y)) > size:
            kept[i] = True
            incident[u].append((v, i))
            incident[v].append((u, i))
    order = list(range(free, vertices))
    parent = {v: (-1, -1) for v in order}
    todo = deque(order)
    while todo:
        u = todo.popleft()
        for v, i in incident[u]:
            if v not in parent:
                parent[v] = (u, i)
                order.append(v)
                todo.append(v)
    result = []
    balance = [[0, 0] for _ in range(vertices)]
    for used, (u, v), (x, y) in zip(kept, edges, flow):
        if not used or u not in parent:
            x, y = 0, 0
        result.append([x, y])
        balance[u][0] -= x
        balance[u][1] -= y
        balance[v][0] += x
        balance[v][1] += y
    for u in reversed(order):
        if u >= free:
            continue
        v, i = parent[u]
        sign = 1 if edges[i][0] == u else -1
        for j, x in enumerate(balance[u]):
            result[i][j] += sign * x
            balance[v][j] += x
    return result


def map_flows(tree, fn):
    if "split" in tree:
        return {**tree, "lower": map_flows(tree["lower"], fn), "upper": map_flows(tree["upper"], fn)}
    if "flows" in tree:
        return {**tree, "flows": [fn(f) for f in tree["flows"]]}
    return tree


def sparse_proof(proof, paths, faces, h):
    support = proof.get("support", faces)

    def thinner(tree, origin=None):
        _, _, free, edges = build_graph(paths, support, INSIDE, origin)
        return map_flows(tree, lambda f: sparse_flow(f, free, edges))

    if "tree" in proof:
        return {**proof, "tree": thinner(proof["tree"])}
    return {**proof, "trees": [thinner(t, B + u) for u, t in enumerate(proof["trees"], start=h)]}


def linear_tree(graph, paths, angle, cap):
    seed = linear_angle_flow(graph, paths, angle, cap)
    if seed is not None and seed[1] > float(RADIUS) - 1e-6:
        return search(graph, lambda _: (None, None), angle, 0, [seed[0]], cap)
    return None


def candidate(paths, faces, angle, h, depth, shell=False, linear=False, linear_only=False):
    if shell:
        graph = build_graph(paths)
        tree = linear_tree(graph, paths, angle, None) if linear else None
        if tree is None and not linear_only:
            flow = free_angle_flow(graph, paths)
            tree = search(graph, lambda u: graph_flow(graph, paths, u), angle, 0,
                          [flow] if flow is not None else ())
        if tree is None:
            return None
        offset = 3 * len(graph[1])
        return {"tree": map_flows(tree, lambda f: f[:offset] + [[0, 0]] * (3 * len(faces)) + f[offset:])}
    if h == INSIDE - 1 and linear:
        cap = origin_radius(h)
        graph = build_graph(paths, faces, INSIDE, B + h)
        tree = linear_tree(graph, paths, angle, cap)
        if tree is not None:
            return {"trees": [tree]}
        if linear_only:
            return None
        f = free_angle_flow(graph, paths, cap)
        tree = search(graph, lambda u: graph_flow(graph, paths, u, cap), angle, depth,
                      [f] if f is not None else (), origin_cap=cap)
        return {"trees": [tree]} if tree is not None else None
    graph = build_graph(paths, faces, INSIDE)
    f = free_angle_flow(graph, paths)
    tree = search(graph, lambda u: graph_flow(graph, paths, u), angle, depth,
                  [f] if f is not None else ())
    if tree is not None:
        return {"tree": tree}
    trees = []
    cap = origin_radius(h)
    for i in range(h, INSIDE):
        graph = build_graph(paths, faces, INSIDE, B + i)
        f = free_angle_flow(graph, paths, cap)
        tree = search(graph, lambda u: graph_flow(graph, paths, u, cap), angle, depth,
                      [f] if f is not None else (), origin_cap=cap)
        if tree is None:
            return None
        trees.append(tree)
    return {"trees": trees}


def solve(task):
    index, belt, fills, depth, try_shell, linear, stars, linear_only = task
    start = time.monotonic()
    meta, paths = parse_belt(belt)
    h = meta[1]
    angle = starting_constraints(paths, CUTS, True)
    shell = shell_mask(paths)
    targets = [(line, faces, face_mask(faces) | shell)
               for line in fills for _, faces in [parse_fill(line)]]
    done, proofs = set(), []
    tried = 0

    def accept(result, line, faces):
        proof = {**result, "fill": line, "windows": True}
        thin = sparse_proof(proof, paths, faces, h)
        try:
            needs, _ = check_proof(thin, paths, faces, CUTS, angle)
            proof = thin
        except ValueError:
            needs, _ = check_proof(proof, paths, faces, CUTS, angle)
        proofs.append(proof)
        done.update(j for j, (_, _, have) in enumerate(targets)
                    if any(have & need == need for need in needs))

    if try_shell:
        line, faces, _ = targets[0]
        result = candidate(paths, faces, angle, h, depth, shell=True,
                           linear=linear, linear_only=linear_only)
        if result is not None:
            accept(result, line, faces)
    if stars and len(done) < len(targets) and h == INSIDE - 1:
        masks = {}
        for j, (_, faces, _) in enumerate(targets):
            mask = sum(1 << u for u in {u for t in faces if h in t for u in t if u != h})
            masks.setdefault(mask, j)
        minimal = [m for m in masks if not any(m != n and m & n == n for n in masks)]
        for mask in sorted(minimal, key=lambda m: (m.bit_count(), m)):
            j = masks[mask]
            if j in done:
                continue
            line, faces, _ = targets[j]
            support = [[u, h] for u in range(h) if mask & (1 << u)]
            result = candidate(paths, support, angle, h, depth, linear=True, linear_only=True)
            if result is not None:
                accept({**result, "support": support}, line, faces)
    for j, (line, faces, _) in enumerate(targets):
        if j in done:
            continue
        tried += 1
        result = candidate(paths, faces, angle, h, depth, linear=linear, linear_only=linear_only)
        if result is not None:
            accept(result, line, faces)
    return ({"index": index, "belt": belt, "proofs": proofs},
            len(targets), len(done), tried, time.monotonic() - start)


def safe_solve(task):
    try:
        return solve(task)
    except MemoryError:
        return task[0]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("belts", type=Path)
    parser.add_argument("fills", type=Path)
    parser.add_argument("patch_cuts", type=Path)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--workers", type=int, default=12)
    parser.add_argument("--depth", type=int, default=1)
    parser.add_argument("--shell", action="store_true")
    parser.add_argument("--linear", action="store_true")
    parser.add_argument("--linear-only", action="store_true")
    parser.add_argument("--stars", action="store_true")
    parser.add_argument("--first", type=int, default=0)
    parser.add_argument("--stop", type=int, default=1000000)
    args = parser.parse_args()
    belts = args.belts.read_text(encoding="utf-8").splitlines()
    partition = defaultdict(list)
    with args.fills.open(encoding="utf-8") as source:
        for line in source:
            line = line.rstrip("\n")
            i = int(line.split("\t", 1)[0])
            if not 0 <= i < len(belts):
                raise ValueError("Unknown belt")
            partition[i].append(line)
    complete = set()
    if args.out.exists():
        with args.out.open(encoding="utf-8") as previous:
            for line in previous:
                p = json.loads(line)
                i = p["index"]
                if i not in partition or belts[i] != p["belt"] or i in complete:
                    raise ValueError("Checkpoint does not match the input")
                complete.add(i)
    tasks = [(i, belts[i], fills, args.depth, args.shell, args.linear or args.linear_only,
              args.stars, args.linear_only)
             for i, fills in sorted(partition.items())
             if args.first <= i < args.stop and i not in complete]
    print(f"belts to solve={len(tasks)}", flush=True)
    with args.out.open("a", encoding="utf-8") as out, get_context("spawn").Pool(
        processes=args.workers, initializer=init, initargs=(str(args.patch_cuts),),
        maxtasksperchild=64,
    ) as pool:
        for item in pool.imap_unordered(safe_solve, tasks):
            if isinstance(item, int):
                print(f"belt {item}: memory allocation failed, checkpoint omitted", flush=True)
                continue
            record, n, covered, tried, elapsed = item
            out.write(json.dumps(record, separators=(",", ":")) + "\n")
            out.flush()
            print(f"belt {record['index']}: excluded {covered}/{n}, "
                  f"solved {tried}, certificates {len(record['proofs'])}, {elapsed:.1f}s", flush=True)


if __name__ == "__main__":
    main()
