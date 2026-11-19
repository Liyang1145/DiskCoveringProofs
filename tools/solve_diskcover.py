#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""Expose the source catalogue and compute fresh rational radius bounds."""
import argparse
import json
from pathlib import Path

from diskcover_grid import solve_grid


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("n", type=int, nargs="?", help="number of covering disks (1–22)")
    parser.add_argument("--all", action="store_true", help="report source status for all orders")
    parser.add_argument("--grid", type=int, help="also compute certified bounds using a grid of spacing 1/GRID")
    parser.add_argument("--max-nodes", type=int, default=20_000, help="total grid search budget")
    args = parser.parse_args()
    if args.all == (args.n is not None):
        parser.error("specify exactly one of n or --all")
    if args.n is not None and not 1 <= args.n <= 22:
        parser.error("n must be between 1 and 22")
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
        if args.grid is not None:
            try:
                result["fresh_certified_bounds"] = solve_grid(args.n, args.grid, args.max_nodes)
            except ValueError as exc:
                parser.error(str(exc))
    print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
