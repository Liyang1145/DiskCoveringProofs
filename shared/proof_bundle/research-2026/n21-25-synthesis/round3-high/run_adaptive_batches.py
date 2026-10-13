"""Serially run and replay bounded adaptive batches for one pending ledger."""
from pathlib import Path
import argparse
import subprocess
import sys
import json

ROOT = Path(__file__).resolve().parent
PY = sys.executable
assert __debug__


def run(*args):
    subprocess.run([PY, "-B", str(ROOT / args[0]), *map(str, args[1:])],
                   cwd=ROOT, check=True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--N", type=int, required=True)
    ap.add_argument("--B", type=int, required=True)
    ap.add_argument("--groups", type=Path, required=True)
    ap.add_argument("--source", type=Path, required=True)
    ap.add_argument("--attempted", type=Path, required=True)
    ap.add_argument("--start", type=int, required=True)
    ap.add_argument("--batches", type=int, required=True)
    ap.add_argument("--count", type=int, default=500)
    ap.add_argument("--limit", type=int, default=501)
    args = ap.parse_args()
    source, attempted, index = args.source, args.attempted, args.start
    for _ in range(args.batches):
        next_index = index + args.count
        routed = ROOT / f"evidence/n{args.N}-B{args.B}-full-unattempted-after{index}-complete-resume1.json"
        output = ROOT / f"evidence/n{args.N}-B{args.B}-full-adaptive-after{index}-next{args.count}-resume1"
        receipt = output / "SUMMARY.json"
        replay = ROOT / f"evidence/n{args.N}-B{args.B}-full-adaptive-after{index}-next{args.count}-replay-resume1.json"
        if not routed.exists():
            run("route_unattempted.py", "--source", source, "--attempted", attempted,
                "--output", routed)
        if not receipt.exists():
            run("probe_groups.py", "--groups", args.groups, "--output", output,
                "--only-pending-from", routed, "--count", args.count, "--limit", args.limit)
        if not replay.exists():
            run("replay_partial_groups.py", "--groups", args.groups,
                "--receipt", receipt, "--output", replay)
        report = json.loads(replay.read_text(encoding="utf8"))
        assert report["verified"] and report["exact_excluded_groups_replayed"] == args.count
        source, attempted, index = routed, receipt, next_index
    print("Adaptive batch loop PASS through", index, "groups", flush=True)


if __name__ == "__main__":
    main()
