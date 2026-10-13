"""Stream full-set comparison, never accept matching partial prefixes."""
from pathlib import Path
import argparse
import json
from stream_catalog import Catalog, sha

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--left", type=Path, required=True)
    ap.add_argument("--right", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    left, right = Catalog(args.left), Catalog(args.right)
    for key in ("N", "B", "scale", "caps", "screen", "orbits"):
        assert left.header[key] == right.header[key]
    count = 0
    for (i, first), (j, last) in zip(left.rows(), right.rows(), strict=True):
        assert i == j and first == last, ("catalogue set discrepancy", i, j)
        count += 1
    assert left.finished and right.finished and count == left.header["orbits"]
    report = {"verified": True, "complete_whole_set_match": True,
              "N": left.header["N"], "B": left.header["B"], "orbits": count,
              "left_sha256": sha(args.left), "right_sha256": sha(args.right),
              "source_sha256": sha(Path(__file__)), "global_optimality_proved": False}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2), encoding="utf8")
    print("FULL catalogue equality PASS", report["N"], report["B"], count, flush=True)


if __name__ == "__main__":
    main()
