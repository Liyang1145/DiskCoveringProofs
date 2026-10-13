"""Validate minimum-boundary-degree root pruning against frozen whole sets."""
from pathlib import Path
from functools import lru_cache
from math import comb, factorial
import argparse
import json
import subprocess
from stream_catalog import Catalog, sha

ROOT = Path(__file__).resolve().parent
assert __debug__


@lru_cache(None)
def labelled(b, i):
    if b == 2:
        return int(i == 0)
    value = sum(comb(i, j)*labelled(k, j)*labelled(b-k+1, i-j)
                for k in range(2, b) for j in range(i+1))
    if i:
        value += i*(labelled(b+1, i-1)-sum(
            comb(i-1, j)*labelled(3, j)*labelled(b, i-1-j) for j in range(i)))
    return value


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    args.output.mkdir(parents=True)
    olddir = ROOT.parent / "evidence/extended-unpruned-regressions"
    old = json.loads((olddir / "SUMMARY.json").read_text())
    tests = []
    for row in old["tests"]:
        B, I = row["B"], row["I"]
        reference = json.loads((olddir / f"N{B+I}-B{B}-noscreen.json").read_text())
        for mode in ("noscreen", "audit-noscreen"):
            path = args.output / f"N{B+I}-B{B}-{mode}.json"
            command = [str(ROOT / "peel_degree.exe"), str(B+I), str(B), str(path),
                       "10000000", "846610", "1761930", "2891603", "0", mode]
            subprocess.run(command, check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            data = json.loads(path.read_text())
            assert data["complete"] and not data["screen"] and data["root_degree_prune"]
            assert data["survivors"] == reference["survivors"]
            assert sum(2*B*factorial(I)//r["stabilizer"] for r in data["survivors"]) == labelled(B, I)
            tests.append({"B": B, "I": I, "mode": mode, "orbits": data["orbits"],
                          "output_sha256": sha(path), "reference_sha256": sha(
                              olddir / f"N{B+I}-B{B}-noscreen.json")})
        print("Minimum-degree root pruning whole-set regression", B, I, "PASS", flush=True)
    report = {"verified": True, "tests": tests, "source_sha256": sha(ROOT / "peel_degree.cpp"),
              "binary_sha256": sha(ROOT / "peel_degree.exe"),
              "theoretical_safety": "choose minimum boundary degree at vertex 0; closed vertices have final degree",
              "global_optimality_proved": False}
    (args.output / "VERIFIED.json").write_text(json.dumps(report, indent=2), encoding="utf8")


if __name__ == "__main__":
    main()
