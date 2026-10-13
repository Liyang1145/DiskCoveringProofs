"""Native complete-family discovery with streamed, bounded-memory validation.

Not an optimality proof. Uses the reviewed peeling induction/safe-pruning
arguments; flags and cardinalities by themselves do not prove completeness.
Writes only a new explicitly scoped output directory.
"""
from pathlib import Path
import argparse
import json
import subprocess
import time
from stream_catalog import Catalog, sha, no_duplicate_keys

ROOT = Path(__file__).resolve().parent
assert __debug__


def read(path):
    return json.loads(path.read_text(encoding="utf8"), object_pairs_hook=no_duplicate_keys)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, choices=(23, 24, 25), required=True)
    ap.add_argument("--B", type=int, required=True)
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--degree-root", action="store_true")
    args = ap.parse_args()
    assert not args.output.exists()
    # Native std::ofstream output is deliberately an ASCII relative argument.
    assert not args.output.is_absolute() and args.output.as_posix().isascii()
    args.output.mkdir(parents=True)
    constantspath = ROOT.parent / f"evidence/core-reduction/constants/n{args.n}.json"
    const = read(constantspath)
    assert const["verified"] and const["N"] == args.n
    assert [args.B, args.n-args.B] in const["families"]
    source = ROOT / "peel_degree.cpp" if args.degree_root else ROOT.parent / "peel_synthesis.cpp"
    binary = ROOT / ("peel_degree.exe" if args.degree_root else "peel_high.exe")
    if args.degree_root:
        controls = read(ROOT / "evidence/degree-pruning-regressions-resume1/VERIFIED.json")
        assert controls["verified"] and controls["source_sha256"] == sha(source)
        assert controls["binary_sha256"] == sha(binary)
    target = args.output / f"N{args.n}-B{args.B}-dfs.json"
    command = [str(binary), str(args.n), str(args.B), str(target),
               str(const["angle_scale"]), *map(str, const["angle_caps"]), "0", "dfs"]
    started = time.monotonic()
    print("Complete necessary-family peeling started", args.n, args.B,
          "no completed claim before termination", flush=True)
    result = subprocess.run(command, cwd=ROOT)
    assert result.returncode == 0, "Native job failed; cannot accept a complete catalogue"
    catalog = Catalog(target)
    head = catalog.header
    assert (head["N"], head["B"], head["mode"]) == (args.n, args.B, "dfs")
    assert head["complete"] and head["screen"]
    assert head["scale"] == const["angle_scale"] and head["caps"] == const["angle_caps"]
    assert not args.degree_root or head["root_degree_prune"]
    previous = None
    count = 0
    for index, row in catalog.rows():
        code = tuple(row["faces"])
        assert previous is None or previous < code
        previous = code
        assert 2*args.B % row["stabilizer"] == 0
        count += 1
        if count % 500000 == 0:
            print("Streamed native catalogue rows validated", count, flush=True)
    assert count == head["orbits"]
    report = {"N": args.n, "B": args.B, "mode": "dfs", "complete": True,
              "orbits": count, "calls": head["calls"], "catalog_sha256": sha(target),
              "source_sha256": sha(source), "binary_sha256": sha(binary),
              "constants_sha256": sha(constantspath),
              "stream_validation_source_sha256": sha(Path(__file__)),
              "stream_reader_sha256": sha(ROOT / "stream_catalog.py"),
              "canonical_root_degree_pruning": args.degree_root,
              "seconds": time.monotonic()-started,
              "catalogue_completeness_requires_written_induction": True,
              "global_optimality_proved": False}
    (args.output / "SUMMARY.json").write_text(json.dumps(report, indent=2), encoding="utf8")
    print("Necessary catalogue completed and streamed", args.n, args.B, count, flush=True)


if __name__ == "__main__":
    main()
