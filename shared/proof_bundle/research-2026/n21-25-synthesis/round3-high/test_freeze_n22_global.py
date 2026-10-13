"""Read-only completion-gate controls; corrupt in-memory copies, never inputs."""
from pathlib import Path
from copy import deepcopy
from contextlib import redirect_stdout
from unittest.mock import patch
import argparse
import io
import json
import sys
import freeze_n22_global as freezer
from stream_catalog import sha

ROOT = Path(__file__).resolve().parent
EV = ROOT / "evidence"
assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    unused = EV / "N22-GLOBAL-preflight-controls-unused-output.json"
    assert not unused.exists() and not unused.with_suffix(".json.building").exists()
    original_read = freezer.read
    rootreport = EV / "n22-interfaces-resume1/evidence/n22/algebraic-check1/root-verified.json"
    localreport = rootreport.parent.parent / "local-isolation-certificate.json"
    cases = [
        ("wrong-shared-evaluator", rootreport, "shared_evaluator_sha256", "0"*64),
        ("root-contraction-not-strict", rootreport, "boxes",
         [{"rho": "1/"+str(10**60), "inclusion": "0", "contraction": "1"},
          {"rho": "1/"+str(10**80), "inclusion": "0", "contraction": "0"}]),
        ("wrong-geometric-root", rootreport, "root_sha256", "0"*64),
        ("wrong-local-radius", localreport, "anchor_radius", "1/5"),
        ("wrong-scalar-root-report", EV / "n22-symmetry-cubic-replay-resume1.json",
         "paid_unique_root_report_sha256", "0"*64),
        ("wrong-six-trig-source", EV / "six-lower-stdlib-resume1.json",
         "trig_source_sha256", "0"*64),
        ("wrong-core-force-kernel", EV / "n22-full-attaining-core-strict-replay-resume2.json",
         "force_kernel_sha256", "0"*64),
        ("wrong-b14-hierarchy", EV / "N22-B14-CATALOGUE-CLOSURE-strict-resume2.json",
         "hierarchy_audit_sha256", "0"*64),
        ("wrong-b14-force-replay", EV / "N22-B14-CATALOGUE-CLOSURE-strict-resume2.json",
         "full_force_replay_sha256", "0"*64),
        ("b15-incomplete", EV / "n22-B15-hierarchy-audit-strict-final-resume2.json",
         "pending_types", 1),
        ("b15-no-force-replay", EV / "n22-B15-hierarchy-audit-strict-final-resume2.json",
         "stages", None),
    ]
    rejected = []
    argv = ["freeze_n22_global.py", "--output", str(unused), "--preflight-only"]
    with patch.object(sys, "argv", argv), redirect_stdout(io.StringIO()):
        freezer.main()
    for label, path, key, value in cases:
        def modified_read(candidate, target=path, field=key, bad=value):
            row = original_read(candidate)
            if Path(candidate).resolve() == target.resolve():
                row = deepcopy(row)
                if field == "stages":
                    row["stages"][-1]["force_replay_sha256"] = None
                else:
                    row[field] = bad
            return row
        with patch.object(freezer, "read", modified_read), patch.object(sys, "argv", argv):
            try:
                with redirect_stdout(io.StringIO()):
                    freezer.main()
            except AssertionError:
                rejected.append(label)
            else:
                raise AssertionError(("invalid interface accepted", label))
        assert not unused.exists() and not unused.with_suffix(".json.building").exists()

    # Check actual B13 pair trees too, rather than only mocked completion flags.
    class DryBindings:
        def add(self, path, expected=None):
            digest = sha(path)
            assert expected is None or expected == digest
            return digest
    audit = original_read(EV / "n22-B13-hierarchy-audit-complete-resume1.json")
    info = audit["stages"][0]
    receipt = EV / "n22-B13-pair-root-resume1/SUMMARY.json"
    replay = EV / "n22-B13-pair-replay-resume1.json"
    freezer.check_stage(13, info, "pair", receipt, replay, DryBindings())
    for label, key, value in [
        ("stage-threshold-mismatch", "threshold", 1),
        ("stage-map-count-mismatch", "maps_checked", info["maps_checked"]+1),
        ("stage-replay-hash-mismatch", "force_replay_sha256", "0"*64),
    ]:
        badinfo = dict(info, **{key: value})
        try:
            freezer.check_stage(13, badinfo, "pair", receipt, replay, DryBindings())
        except AssertionError:
            rejected.append(label)
        else:
            raise AssertionError(("invalid stage accepted", label))
    result = {"verified": True, "positive_controls": 2,
              "negative_controls_rejected": rejected,
              "frozen_inputs_modified": False, "snapshot_written": False,
              "source_sha256": sha(Path(__file__)),
              "freezer_sha256": sha(ROOT / "freeze_n22_global.py"),
              "scope": "completion-gate and input-binding controls, not mathematical proof"}
    args.output.write_text(json.dumps(result, indent=2), encoding="utf8")
    print("N22 freezer controls PASS:", len(rejected), "negative controls; immutable inputs untouched",
          flush=True)


if __name__ == "__main__":
    main()
