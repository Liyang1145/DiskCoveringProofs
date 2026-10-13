"""Reject forged short-path angle cycles; no solver involved."""
from pathlib import Path
from copy import deepcopy
import argparse
import json
from angle_obstructions import read, constants_gate, verify_cycle
from stream_catalog import sha

ROOT = Path(__file__).resolve().parent
assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--certificate", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    certificate = read(args.certificate)
    constants = read(ROOT.parent / "evidence/core-reduction/constants/n25.json")
    constants_gate(constants)
    row = next(r for r in certificate["outcomes"] if r["status"] == "excluded"
               and any(e["kind"] == "short-path" for e in r["cycle"]))
    B, masks, centers = certificate["B"], row["faces"], row["centers"]
    assert verify_cycle(B, centers, masks, row["cycle"], constants) == row["exact_cycle_check"]
    bad = []
    cycle = deepcopy(row["cycle"])
    cycle[0]["weight"] += 1
    bad.append(("wrong-integer-bound", cycle, masks))
    cycle = deepcopy(row["cycle"])
    cycle[0]["v"] = (cycle[0]["v"]+1) % B
    bad.append(("broken-cycle-incidence", cycle, masks))
    cycle = deepcopy(row["cycle"])
    edge = next(e for e in cycle if e["kind"] == "short-path")
    edge["path"][0] = centers
    bad.append(("out-of-range-path", cycle, masks))
    cycle = deepcopy(row["cycle"])
    edge = next(e for e in cycle if e["kind"] == "short-path")
    edge["direction"] *= -1
    bad.append(("wrong-short-arc-direction", cycle, masks))
    cycle = deepcopy(row["cycle"])
    edge = next(e for e in cycle if e["kind"] == "short-path")
    edge["path"] = [edge["path"][0]]*4
    bad.append(("too-long-unpaid-path", cycle, masks))
    bad.append(("missing-all-face-witnesses", deepcopy(row["cycle"]), []))
    bad.append(("empty-cycle", [], masks))
    rejected = []
    for label, cycle, faces in bad:
        try:
            verify_cycle(B, centers, faces, cycle, constants)
        except (AssertionError, IndexError, KeyError):
            rejected.append(label)
        else:
            raise AssertionError(("forged angle certificate accepted", label))
    args.output.write_text(json.dumps({
        "verified": True, "certificate_sha256": sha(args.certificate),
        "source_sha256": sha(Path(__file__)),
        "angle_checker_sha256": sha(ROOT / "angle_obstructions.py"),
        "negative_controls_rejected": rejected, "global_optimality_proved": False,
    }, indent=2)+"\n", encoding="utf8")
    print("Angle-cycle negative controls PASS:", len(rejected), flush=True)


if __name__ == "__main__":
    main()
