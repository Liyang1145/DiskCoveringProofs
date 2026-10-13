"""Mechanical schema/provider instantiation of the frozen leaf-only refinement."""
from pathlib import Path
import json
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "round3-high"))
from stream_catalog import sha

assert __debug__


def main():
    specifications = [
        ("refine_paid_hole_leaves.py", "refine_linked_collar_leaves.py", [
            ('"proof-paid-simple-hole-independent-replay-v1"',
             '"proof-paid-linked-general-collar-independent-replay-v1"'),
            ('"replay_paid_hole.py"', '"replay_linked_general_collar.py"'),
        ]),
        ("replay_refined_hole_leaves.py", "replay_refined_linked_leaves.py", [
            ("from proof_paid_hole_kernel import replay", "from linked_general_collar_kernel import replay"),
            ('"proof-paid-simple-hole-independent-replay-v1"',
             '"proof-paid-linked-general-collar-independent-replay-v1"'),
            ('"replay_paid_hole.py"', '"replay_linked_general_collar.py"'),
            ('"refine_paid_hole_leaves.py"', '"refine_linked_collar_leaves.py"'),
            ('"proof_paid_hole_kernel.py"', '"linked_general_collar_kernel.py"'),
            ('"PROOF-PAID-HOLE-SOURCE.md"', '"GENERAL-COLLAR-FILLING-SOURCE.md"'),
            ('"same-topology-hole-force-refinement-exact-v1"',
             '"same-topology-linked-collar-force-refinement-exact-v1"'),
        ]),
    ]
    report = ROOT / "linked-leaf-refinement-source-derivation.json"
    assert not report.exists() and all(not (ROOT / target).exists() for _, target, _ in specifications)
    records = []
    for source, target, replacements in specifications:
        original = (ROOT / source).read_text(encoding="utf8")
        text = original
        for before, after in replacements:
            expected = 2 if target == "replay_refined_linked_leaves.py" and before == '"refine_paid_hole_leaves.py"' else 1
            assert text.count(before) == expected, (target, before, text.count(before))
            text = text.replace(before, after)
        # Inverting every substitution recovers the exact original. No force
        # proposal, node state, branch partition, or topology comparison changes.
        reverse = text
        for before, after in reversed(replacements):
            reverse = reverse.replace(after, before)
        assert reverse == original
        (ROOT / target).write_text(text, encoding="utf8", newline="\n")
        records.append({"source": source, "source_sha256": sha(ROOT / source),
                        "target": target, "target_sha256": sha(ROOT / target),
                        "replacements": replacements, "exact_inverse_equals_frozen_source": True})
    report.write_text(json.dumps({
        "verified": True, "schema": "linked-leaf-refinement-mechanical-derivation-v1",
        "source_sha256": sha(Path(__file__)), "files": records,
        "only_schema_source_identity_and_complete_filling_provider_changed": True,
        "only_original_FULL_PENDING_leaves_can_change": True,
        "all_other_topology_states_payments_and_child_lists_unchanged": True,
        "global_optimality_proved": False,
    }, indent=2)+"\n", encoding="utf8")
    print("Linked-collar leaf refinement mechanically derived; exact inverse PASS", flush=True)


if __name__ == "__main__":
    main()
