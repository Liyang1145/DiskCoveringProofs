"""New native build of the frozen generalized peeling source, one family."""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import time

ROOT = Path(__file__).resolve().parent
assert __debug__


def sha(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--n", type=int, choices=(21, 22, 23, 24, 25), required=True)
    p.add_argument("--B", type=int, required=True)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--mode", choices=("dfs", "audit", "noscreen", "audit-noscreen"), default="dfs")
    p.add_argument("--limit", type=int, default=0)
    p.add_argument("--degree-root", action="store_true")
    args = p.parse_args()
    assert not args.output.exists()
    args.output.mkdir(parents=True)
    source = ROOT / "peel_degree.cpp" if args.degree_root else ROOT.parent / "peel_synthesis.cpp"
    binary = ROOT / ("peel_degree.exe" if args.degree_root else "peel_high.exe")
    assert binary.exists()
    if args.degree_root:
        regressions = json.loads((ROOT / "evidence/degree-pruning-regressions-resume1/VERIFIED.json").read_text())
        assert regressions["verified"] and regressions["source_sha256"] == sha(source)
        assert regressions["binary_sha256"] == sha(binary)
    constants_path = ROOT.parent / f"evidence/core-reduction/constants/n{args.n}.json"
    constants = json.loads(constants_path.read_text(encoding="utf8"))
    assert constants["verified"] and constants["N"] == args.n
    assert any(row[0] == args.B for row in constants["families"])
    target = args.output / f"N{args.n}-B{args.B}-{args.mode}.json"
    command = [str(binary), str(args.n), str(args.B), str(target),
               str(constants["angle_scale"]), *map(str, constants["angle_caps"]),
               str(args.limit), args.mode]
    print("Peeling", args.n, args.B, args.mode, "started; no completed claim before termination", flush=True)
    started = time.monotonic()
    result = subprocess.run(command)
    if result.returncode:
        assert not target.exists()
        report = {"N": args.n, "B": args.B, "mode": args.mode,
                  "complete": False, "returncode": result.returncode}
    else:
        data = json.loads(target.read_text(encoding="utf8"))
        assert data["complete"] and data["N"] == args.n and data["B"] == args.B
        assert data["caps"] == constants["angle_caps"]
        assert len(data["survivors"]) == data["orbits"]
        report = {"N": args.n, "B": args.B, "mode": args.mode, "complete": True,
                  "orbits": data["orbits"], "calls": data["calls"], "catalog_sha256": sha(target)}
    report.update(seconds=time.monotonic()-started, source_sha256=sha(source),
                  binary_sha256=sha(binary), constants_sha256=sha(constants_path),
                  canonical_root_degree_pruning=args.degree_root,
                  global_optimality_proved=False)
    (args.output / "SUMMARY.json").write_text(json.dumps(report, indent=2), encoding="utf8")
    print(json.dumps(report, indent=2), flush=True)


if __name__ == "__main__":
    main()
