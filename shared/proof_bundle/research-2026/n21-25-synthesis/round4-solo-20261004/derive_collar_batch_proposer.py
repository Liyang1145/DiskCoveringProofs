"""Use the frozen force proposer, permitting N21 storage controls without a core file."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    original = ROOT.parent / "round3-high/probe_groups.py"
    target, reportpath = ROOT / "probe_collar_batches.py", ROOT / "collar-batch-proposer-derivation.json"
    assert not target.exists() and not reportpath.exists()
    old = original.read_text(encoding="utf8")
    changes = [
        ("import exact_graph as exact",
         'import sys\nsys.path.insert(0, str(Path(__file__).resolve().parent.parent / "round3-high"))\n'
         "import exact_graph as exact"),
        ("ROOT = Path(__file__).resolve().parent",
         'ROOT = Path(__file__).resolve().parent.parent / "round3-high"'),
        ("    if N < 25:\n        candidate =",
         "    if N == 21:\n"
         "        # Only small storage controls use N21; its absent core file is not\n"
         "        # fabricated. Exact force acceptance still checks every exclusion.\n"
         "        candidateB, fullfaces = None, None\n"
         "    elif N < 25:\n        candidate ="),
    ]
    text, counts = old, []
    for before, after in changes:
        assert text.count(before) == 1
        counts.append(1)
        text = text.replace(before, after)
    target.write_text(text, encoding="utf8", newline="\n")
    reportpath.write_text(json.dumps({
        "verified_mechanical_derivation": True,
        "original_source_sha256": sha(original), "derived_source_sha256": sha(target),
        "source_sha256": sha(Path(__file__)), "changes": changes, "occurrence_counts": counts,
        "force_construction_and_exact_acceptance_unchanged": True,
        "N25_candidate_control_unchanged": True, "N21_no_candidate_core_theorem_asserted": True,
        "global_optimality_proved": False,
    }, indent=2)+"\n", encoding="utf8")


if __name__ == "__main__":
    main()
