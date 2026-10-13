"""True whole-family positive and true unfinished lower-limit rejection."""
from pathlib import Path
import argparse
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "round3-high"))
from stream_catalog import sha
from n25_outer_search import publish, read
from audit_complete_origin_finer_with_direct import add_family
from linked_general_collar_kernel import replay

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    family = ROOT / "n25-B15-all23196-complete-fillings-and-fresh-merge-20261005-v1/batch-000164/parent-0131898"
    proof = ROOT / "n25-B15-parent131898-finer1001-PROPOSAL-20261005-v1.json"
    exact = ROOT / "n25-B15-parent131898-finer1001-EXACT-20261005-v1.json"
    unfinished = ROOT / "n25-B15-parent131898-finer511-PROPOSAL-20261005-v1.json"
    unfinished_exact = ROOT / "n25-B15-parent131898-finer511-EXACT-20261005-v1.json"
    constants = read(ROOT.parent / "evidence/core-reduction/constants/n25.json")
    assert replay(proof, constants)["all_full_simple_disk_completions_strictly_paid"]
    assert not replay(unfinished, constants)["all_full_simple_disk_completions_strictly_paid"]
    additions, files = {}, {}
    add_family(additions, 131898, family, proof, exact, files)
    assert set(additions) == {131898}
    rejected = []
    cases = (
        ("duplicate-parent-payment", additions, 131898, family, proof, exact),
        ("bool-not-parent-integer", {}, True, family, proof, exact),
        ("actual-511-unfinished-family", {}, 131898, family, unfinished, unfinished_exact),
        ("mixed-proof-and-unfinished-replay", {}, 131898, family, proof, unfinished_exact),
        ("wrong-original-family", {}, 131898,
         ROOT / "n25-B15-all23196-complete-fillings-and-fresh-merge-20261005-v1/batch-000000/parent-0000000",
         proof, exact),
        ("out-of-workspace-proof", {}, 131898, family, ROOT.parent / "outside-proof.json", exact),
    )
    for label, selected, pid, testfamily, testproof, testexact in cases:
        try:
            add_family(selected, pid, testfamily, testproof, testexact, {})
        except (AssertionError, KeyError, ValueError, FileNotFoundError):
            rejected.append(label)
        else:
            raise AssertionError(("invalid standalone deeper family accepted", label))
    output.mkdir()
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "standalone-deeper-finer-family-controls-v1",
        "actual_complete_family_tree_freshly_replayed": True,
        "actual_lower_limit_unpaid_tree_freshly_replayed_and_not_paid": True,
        "negative_controls_rejected": rejected,
        "proof_sha256": sha(proof), "exact_sha256": sha(exact),
        "unfinished_proof_sha256": sha(unfinished),
        "source_sha256": sha(Path(__file__)),
        "audit_source_sha256": sha(ROOT / "audit_complete_origin_finer_with_direct.py"),
        "all_parent_partition_and_old_positive_tree_replays_still_required": True,
        "global_optimality_proved": False,
    })
    print("Standalone deeper-family controls PASS:", len(rejected), "rejections", flush=True)


if __name__ == "__main__":
    main()
