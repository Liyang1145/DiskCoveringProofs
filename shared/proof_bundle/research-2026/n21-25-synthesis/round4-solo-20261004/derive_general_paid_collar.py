"""Preserve exact force construction/replay, replace only topology child provider."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    reportpath = ROOT / "general-paid-collar-source-derivation.json"
    assert not reportpath.exists()
    reports = []
    for originalname, targetname in (
        ("proof_paid_hole_kernel.py", "general_paid_collar_kernel.py"),
        ("prove_paid_hole.py", "prove_general_collar.py"),
        ("replay_paid_hole.py", "replay_general_collar.py"),
    ):
        original, target = ROOT / originalname, ROOT / targetname
        assert not target.exists()
        old = original.read_text(encoding="utf8")
        changes = [
            ("proof-paid-simple-hole-branch-tree-v1", "proof-paid-general-collar-branch-tree-v1"),
            ("proof_paid_hole_kernel", "general_paid_collar_kernel"),
            ("prove_paid_hole.py", "prove_general_collar.py"),
        ]
        if originalname == "proof_paid_hole_kernel.py":
            start, end = old.index("def start_states("), old.index("\ndef all_complete_codes(")
            changes.append((old[start:end], "from general_collar_filling import start_states, children\n"))
        if originalname == "replay_paid_hole.py":
            changes.extend([
                ("proof-paid-simple-hole-independent-replay-v1", "proof-paid-general-collar-independent-replay-v1"),
                ('ROOT / "SIMPLE-COLLAR-COMPLETION-SOURCE.md",',
                 'ROOT / "SIMPLE-COLLAR-COMPLETION-SOURCE.md", ROOT / "general_collar_filling.py",\n'
                 '        ROOT / "GENERAL-COLLAR-FILLING-SOURCE.md", ROOT / "general-paid-collar-source-derivation.json",'),
            ])
        text, applied = old, []
        for before, after in changes:
            count = text.count(before)
            if not count:
                continue
            text = text.replace(before, after)
            applied.append({"before": before, "after": after, "occurrences": count})
        target.write_text(text, encoding="utf8", newline="\n")
        reports.append({"original": originalname, "derived": targetname,
                        "original_sha256": sha(original), "derived_sha256": sha(target), "changes": applied})
    reportpath.write_text(json.dumps({
        "verified_mechanical_derivation": True, "files": reports,
        "source_sha256": sha(Path(__file__)), "topology_provider_sha256": sha(ROOT / "general_collar_filling.py"),
        "all_exact_force_construction_and_acceptance_checks_preserved": True,
        "new_domain_requires_general_collar_source_and_controls": True, "global_optimality_proved": False,
    }, indent=2)+"\n", encoding="utf8")


if __name__ == "__main__":
    main()
