#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""Report disk-cover proofs or run fresh exact proofs and rational bounds."""
import argparse
import json
from pathlib import Path

from diskcover_global import solve_global
from diskcover_grid import solve_grid


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("n", type=int, nargs="?", help="number of covering disks (1–22)")
    parser.add_argument("--all", action="store_true", help="report source status for all orders")
    parser.add_argument("--grid", type=int, help="also compute certified bounds using a grid of spacing 1/GRID")
    parser.add_argument("--certified-upper", action="store_true",
                        help="replay a bundled upper witness (currently n=19 and n=20; not a global proof)")
    parser.add_argument("--max-nodes", type=int, default=20_000, help="total grid search budget")
    parser.add_argument("--require-global-proof", action="store_true",
                        help="return a self-contained exact proof, or exit 2 if unavailable")
    parser.add_argument("--proof-data-dir", type=Path, metavar="DIR",
                        help="cache for pinned proof input data (default: build/proof-data in the repository)")
    parser.add_argument("--offline", action="store_true",
                        help="never download missing proof input data")
    parser.add_argument("--proof-workers", type=int, choices=range(1, 7), metavar="1–6",
                        help="worker cap for parallel exact proof replays (default: 4)")
    args = parser.parse_args(argv)
    if args.all == (args.n is not None):
        parser.error("specify exactly one of n or --all")
    if args.n is not None and not 1 <= args.n <= 22:
        parser.error("n must be between 1 and 22")
    if args.require_global_proof and (args.all or args.grid is not None or args.certified_upper):
        parser.error("--require-global-proof cannot be combined with --all, --grid or --certified-upper")
    if args.certified_upper and args.n not in (19, 20):
        parser.error("--certified-upper requires n=19 or n=20")
    replay_options = args.proof_data_dir is not None or args.offline or args.proof_workers is not None
    if replay_options and not args.require_global_proof:
        parser.error("proof-data options require --require-global-proof")
    if args.require_global_proof:
        from diskcover_replay import ReplayError, solve_replayed, supports_replay
        if supports_replay(args.n):
            data_dir = args.proof_data_dir or (Path(__file__).resolve().parents[1] / "build" / "proof-data")
            try:
                result = solve_replayed(args.n, data_dir, offline=args.offline,
                                        workers=args.proof_workers or 4)
            except (ReplayError, OSError) as exc:
                parser.exit(1, f"n={args.n}: exact proof replay did not complete: {exc}\n")
        else:
            if replay_options:
                parser.error("proof-data options apply only to n=13,16,17,18,19")
            result = solve_global(args.n)
        if result is None:
            parser.exit(2, f"n={args.n}: no self-contained global proof implemented; no exact solution returned\n")
        print(json.dumps(result, ensure_ascii=False, indent=2))
        return
    if args.all and args.grid is not None:
        parser.error("--grid requires an individual order")
    if args.max_nodes < 0:
        parser.error("--max-nodes must be nonnegative")
    path = Path(__file__).with_name("diskcover_catalog.json")
    catalog = json.loads(path.read_text(encoding="utf-8"))
    records = catalog if isinstance(catalog, list) else catalog["orders"]
    if args.all:
        result = records
    else:
        result = {"source": next(entry for entry in records if entry["n"] == args.n)}
        if args.certified_upper:
            if args.n == 19:
                from diskcover_n19_upper import check_n19_upper as check_upper
            else:
                from diskcover_n20_upper import check_n20_upper as check_upper
            result["fresh_certified_upper"] = check_upper()
        if args.grid is not None:
            try:
                result["fresh_certified_bounds"] = solve_grid(args.n, args.grid, args.max_nodes)
            except ValueError as exc:
                parser.error(str(exc))
    print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
