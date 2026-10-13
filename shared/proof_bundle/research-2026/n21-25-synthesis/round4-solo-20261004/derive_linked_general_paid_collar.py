"""Preserve force logic and add the explicitly proved necessary link checks."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    reportpath = ROOT / "linked-general-paid-collar-source-derivation.json"
    assert not reportpath.exists()
    reports = []
    for oldname, newname in (
        ("general_paid_collar_kernel.py", "linked_general_collar_kernel.py"),
        ("prove_general_collar.py", "prove_linked_general_collar.py"),
        ("replay_general_collar.py", "replay_linked_general_collar.py"),
    ):
        original, target = ROOT / oldname, ROOT / newname
        assert not target.exists()
        changes = [
            ("general_paid_collar_kernel", "linked_general_collar_kernel"),
            ("from general_collar_filling import start_states, children",
             "from general_collar_filling_linked import start_states, children"),
            ("prove_general_collar.py", "prove_linked_general_collar.py"),
            ("proof-paid-general-collar-branch-tree-v1", "proof-paid-linked-general-collar-branch-tree-v1"),
            ("proof-paid-general-collar-independent-replay-v1", "proof-paid-linked-general-collar-independent-replay-v1"),
            ('ROOT / "general_collar_filling.py",',
             'ROOT / "general_collar_filling.py", ROOT / "general_collar_filling_linked.py",\n'
             '        ROOT / "linked-general-paid-collar-source-derivation.json",'),
        ]
        text, applied = original.read_text(encoding="utf8"), []
        for before, after in changes:
            count = text.count(before)
            if count:
                text = text.replace(before, after)
                applied.append({"before": before, "after": after, "occurrences": count})
        target.write_text(text, encoding="utf8", newline="\n")
        reports.append({"original": oldname, "derived": newname, "original_sha256": sha(original),
                        "derived_sha256": sha(target), "changes": applied})
    reportpath.write_text(json.dumps({
        "verified_mechanical_derivation": True, "files": reports, "source_sha256": sha(Path(__file__)),
        "link_provider_sha256": sha(ROOT / "general_collar_filling_linked.py"),
        "exact_force_construction_and_acceptance_unchanged": True,
        "global_optimality_proved": False,
    }, indent=2)+"\n", encoding="utf8")


if __name__ == "__main__":
    main()
