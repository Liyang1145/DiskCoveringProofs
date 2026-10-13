"""Stdlib replays for the SAME endpoint graph with a freshly larger local ball."""
from pathlib import Path
from fractions import Fraction as F
from contextlib import contextmanager
import argparse
import gzip
import json
import sys
import replay_n25_endpoint_domain as baseline
from replay_candidate import local
from stream_catalog import sha, no_duplicate_keys

ROOT = Path(__file__).resolve().parent
BASE_INPUTS = baseline.inputs
assert __debug__


def read(path):
    return json.loads(path.read_text(encoding="utf8"), object_pairs_hook=no_duplicate_keys)


def inputs(sign):
    constants, masks, _, bound, oldcore = BASE_INPUTS(sign)
    path = ROOT / "evidence/n25-endpoint-tight-isolation-gamma2000-resume1/REPORT.json"
    repeated = ROOT / "evidence/n25-endpoint-tight-isolation-gamma2000-replay-resume1/REPORT.json"
    certificate = read(path)
    assert certificate["verified"] and path.read_bytes() == repeated.read_bytes()
    assert certificate["source_sha256"] == sha(ROOT / "n25_endpoint_tight_isolation.py")
    assert certificate["rounding_source_sha256"] == sha(ROOT / "n25_anchor_isolation.py")
    assert certificate["geometry_sha256"] == bound["geometry"]
    assert certificate["fibre_report_sha256"] == bound["fibre"]
    assert certificate["stress_character_sha256"] == bound["character"]
    matches = [row for row in certificate["cores"] if row["parameter_sign"] == sign]
    assert len(matches) == 1
    core = matches[0]
    assert core["verified"] and core["positive_leading_principal_minors"] == 120
    assert core["gamma"] == 2000 and F(core["nu"]) == F(21, 5000)
    assert F(core["lambda"]) == F(1, 5000) and F(core["anchor_radius"]) == F(1, 20)
    assert F(core["isolation_margin"]) == F(59, 2500000)
    for key in ("points_Qsqrt2", "faces", "edges", "weights_Qsqrt2",
                "free_circle_multipliers_Qsqrt2", "old_nodes_retained"):
        assert core[key] == oldcore[key], ("changed reduced-core mathematical object", key)
    # The original independently implemented anchor enclosures remain identical.
    from math import isqrt
    scale = 10**80
    lower = isqrt(2*scale*scale)
    assert lower**2 < 2*scale*scale < (lower+1)**2
    def enclosure(v):
        a, b = map(F, v)
        first, last = a+b*F(lower, scale), a+b*F(lower+1, scale)
        return min(first, last), max(first, last)
    anchors = [[enclosure(v) for v in point] for point in core["points_Qsqrt2"][1:16]]
    bound = dict(bound, base_local=bound["local"], local=sha(path),
                 local_repeat=sha(repeated),
                 tight_isolation_source=sha(ROOT / "n25_endpoint_tight_isolation.py"),
                 baseline_partition_source=sha(ROOT / "replay_n25_endpoint_domain.py"))
    return constants, masks, local(anchors, F(1, 20)), bound, core


def replay(tree):
    # Share the inspected complete partition checker, not a solver or old PASS.
    original = baseline.inputs
    assert original is BASE_INPUTS
    baseline.inputs = inputs
    try:
        return baseline.replay(tree)
    finally:
        baseline.inputs = original


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--tree", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    with gzip.open(args.tree, "rt", encoding="utf8") as stream:
        tree = json.load(stream, object_pairs_hook=no_duplicate_keys)
    result = replay(tree)
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath"))
    result.update(tree_sha256=sha(args.tree), source_sha256=sha(Path(__file__)),
                  anchor_radius="1/20", local_theorem_same_core_newly_replayed=True,
                  no_optimizer_imported=True)
    args.output.write_text(json.dumps(result, indent=2), encoding="utf8")
    print("N25 larger-ball endpoint exact replay PASS; unpaid", result["pending_boxes"],
          "whole-domain", result["entire_angle_domain_proved"], flush=True)


if __name__ == "__main__":
    main()
