"""Generate exact shell exclusions for b>=15 using numeric LP flow proposals."""

import argparse
import json
import os
from contextlib import nullcontext
from multiprocessing import get_context
from pathlib import Path

os.environ["OMP_NUM_THREADS"] = "1"
os.environ["OPENBLAS_NUM_THREADS"] = "1"

from find_belt_geometry import anchored_search, free_angle_flow, search
from linear_flow14 import linear_angle_flow, mean_gauge
from verify_belt_geometry import closure, verify_tree
from verify_outer_windows import model_windows
from verify_patch14 import RADIUS
from verify_shells import prepare


def init(n, b, windows, refine, depth, use_mean=False):
    global N, B, WINDOWS, REFINE, DEPTH, USE_MEAN
    N, B, REFINE, DEPTH = n, b, refine, depth
    WINDOWS = windows
    USE_MEAN = use_mean


def solve(task):
    i, line = task
    h, graph, edges = prepare(line, N, B, WINDOWS)
    dist = closure(edges,B)
    if dist is None:
        tree = {"cycle": True}
    else:
        seed = linear_angle_flow(graph, None, edges, boundary=B, iterations=5 if REFINE else 3)
        tree = None
        if seed is not None and seed[1] > float(RADIUS) - 1e-6:
            tree = search(graph, lambda _: (None, None), edges, 0, [seed[0]], boundary=B)
        if tree is None and REFINE:
            fit = free_angle_flow(graph, None, boundary=B, with_prefix=True)
            if fit is not None and fit[3] > float(RADIUS)**2 - 1e-9:
                mean = mean_gauge(dist) if USE_MEAN else None
                tree = anchored_search(graph,edges,None,B,fit,DEPTH,mean_anchor=mean)
        if tree is None:
            return None
    verify_tree(tree, graph, edges, boundary=B)
    return {"index": i, "shell": line, "tree": tree}


def safe_solve(task):
    try:
        return solve(task)
    except MemoryError:
        return None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("shells", type=Path)
    parser.add_argument("windows", type=Path)
    parser.add_argument("--disks", type=int, required=True)
    parser.add_argument("--boundary", type=int, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--workers", type=int, default=8)
    parser.add_argument("--first", type=int, default=0)
    parser.add_argument("--stop", type=int, default=1000000)
    parser.add_argument("--refine", action="store_true")
    parser.add_argument("--depth", type=int, default=0)
    parser.add_argument("--resume", action="store_true")
    parser.add_argument("--mean-gauge", action="store_true")
    args = parser.parse_args()
    rows = args.shells.read_text(encoding="utf-8").splitlines()
    done = set()
    if args.resume and args.out.exists():
        with args.out.open(encoding="utf-8") as old:
            for line in old:
                record = json.loads(line)
                i = record["index"]
                if i in done or not 0 <= i < len(rows) or record["shell"] != rows[i]:
                    raise ValueError("Shell checkpoint does not match the enumerated input")
                done.add(i)
    indices = range(args.first, min(args.stop, len(rows)))
    total = len(indices) - sum(i in indices for i in done)
    tasks = ((i, rows[i]) for i in indices if i not in done)
    windows = model_windows(args.windows,args.disks,args.boundary)
    count = 0
    initargs = (args.disks,args.boundary,windows,args.refine,args.depth,args.mean_gauge)
    if args.workers == 1:
        init(*initargs)
        workers = nullcontext(None)
    else:
        workers = get_context("spawn").Pool(processes=args.workers, initializer=init,
                                           initargs=initargs, maxtasksperchild=1000)
    with args.out.open("a" if args.resume else "w", encoding="utf-8") as out, workers as pool:
        results = map(safe_solve,tasks) if pool is None else pool.imap_unordered(safe_solve,tasks,chunksize=5)
        for j, result in enumerate(results, 1):
            if result is not None:
                out.write(json.dumps(result, separators=(",", ":")) + "\n")
                count += 1
            if j % 500 == 0 or j == total:
                out.flush()
                print(f"tried={j}/{total} proved={count}", flush=True)


if __name__ == "__main__":
    main()
