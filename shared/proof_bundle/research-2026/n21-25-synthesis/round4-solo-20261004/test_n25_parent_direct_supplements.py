"""Actual accepted B16/B17 family bindings and finite partition refusals."""
from pathlib import Path
from copy import deepcopy
from io import StringIO
import argparse
import json

from audit_n25_parent_direct_supplements import (
    ROOT, HIGH, read, publish, sha, add_family, check_source, valid_payment_partition)

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    examples = [
        (47808, ROOT / "n25-B16-all29556-library-parent-gapped-fillings-solo-v1/batch-000091/parent-0047808",
         ROOT / "n25-B16-p47808-f511-proposal-v1.json", ROOT / "n25-B16-p47808-f511-exact-v1.json"),
        *[(pid, ROOT / f"n25-B17-f1/batch-000005/parent-{pid:07}",
           ROOT / f"n25-B17-p{pid}-f511-proposal-v1.json",
           ROOT / f"n25-B17-p{pid}-f511-exact-v1.json") for pid in (5669, 5679, 5778)],
    ]
    constantshash = sha(HIGH.parent / "evidence/core-reduction/constants/n25.json")
    positives = []
    for pid, family, proofpath, exactpath in examples:
        additions, files = {}, {}
        add_family(additions, pid, family, proofpath, exactpath, files)
        assert set(additions) == {pid}
        collar, payload, exact = map(read, (family / "INPUT-COLLAR.json", proofpath, exactpath))
        row = {"id": pid, "centers": collar["centers"], "faces": collar["faces"]}
        check_source(row, collar, payload, exact, 25, collar["B"],
                     collar["source_snapshot_sha256"], constantshash)
        positives.append({"parent": pid, "B": collar["B"], "proof_sha256": sha(proofpath),
                          "exact_sha256": sha(exactpath)})
    pid, family, proofpath, exactpath = examples[0]
    collar, payload, exact = map(read, (family / "INPUT-COLLAR.json", proofpath, exactpath))
    row = {"id": pid, "centers": collar["centers"], "faces": collar["faces"]}
    rejected = []
    for label, field, value in (
        ("wrong-parent-source-index", "complete_parent_index", pid+1),
        ("wrong-original-snapshot-binding", "source_snapshot_sha256", "altered"),
        ("wrong-N", "N", 24), ("wrong-B", "B", 17),
        ("weakened-collar-center-count", "centers", 23),
        ("omitted-whole-source-face", "faces", collar["faces"][:-1]),
    ):
        changed = deepcopy(collar)
        changed[field] = value
        try:
            check_source(row, changed, payload, exact, 25, 16,
                         collar["source_snapshot_sha256"], constantshash)
        except (AssertionError, ValueError, KeyError):
            rejected.append(label)
        else:
            raise AssertionError(("bad source collar accepted", label))
    for label, field, value in (
        ("proof-wrong-whole-outer-face-set", "collar_faces", payload["collar_faces"][:-1]),
        ("proof-wrong-N", "N", 24), ("proof-wrong-B", "B", 17),
        ("proof-wrong-constants", "constants_sha256", "altered"),
    ):
        changed = deepcopy(payload)
        changed[field] = value
        try:
            check_source(row, collar, changed, exact, 25, 16,
                         collar["source_snapshot_sha256"], constantshash)
        except (AssertionError, ValueError, KeyError):
            rejected.append(label)
        else:
            raise AssertionError(("bad full source proof accepted", label))
    try:
        additions, files = {}, {}
        add_family(additions, pid, family, proofpath, exactpath, files)
        add_family(additions, pid, family, proofpath, exactpath, files)
    except AssertionError:
        rejected.append("duplicate-source-parent-supplement")
    else:
        raise AssertionError("duplicate supplement accepted")
    paid = [{"parent_index": 0}, {"parent_index": 2}]
    pending = [{"parent_index": 1}, {"parent_index": 3}]

    def partition(paidrows, pendingrows):
        return list(valid_payment_partition(
            4, StringIO("".join(json.dumps(row)+"\n" for row in paidrows)),
            StringIO("".join(json.dumps(row)+"\n" for row in pendingrows))))

    assert len(partition(paid, pending)) == 4
    for label, paidrows, pendingrows in (
        ("missing-full-parent-row", paid, pending[:-1]),
        ("overlapping-old-paid-and-pending", paid, [{"parent_index": 0}]+pending),
        ("duplicate-old-paid-row", paid[:1]+paid, pending),
        ("extra-full-parent-row", paid+[{"parent_index": 4}], pending),
    ):
        try:
            partition(paidrows, pendingrows)
        except AssertionError:
            rejected.append(label)
        else:
            raise AssertionError(("invalid full partition accepted", label))
    output.mkdir()
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "N25-B16-B17-direct-parent-incremental-controls-v1",
        "real_independently_accepted_B16_B17_families_checked": positives,
        "negative_controls_rejected": rejected,
        "audit_source_sha256": sha(ROOT / "audit_n25_parent_direct_supplements.py"),
        "frozen_deeper_family_checker_sha256": sha(ROOT / "audit_complete_origin_finer_with_direct.py"),
        "source_sha256": sha(Path(__file__)),
        "positive_functional_checks_not_complete_parent_payment_adoption": True,
        "global_optimality_proved": False,
    })
    print("N25 B16/B17 direct supplemental source/partition controls passed:",
          len(rejected), "refusals; four real family bindings", flush=True)


if __name__ == "__main__":
    main()
