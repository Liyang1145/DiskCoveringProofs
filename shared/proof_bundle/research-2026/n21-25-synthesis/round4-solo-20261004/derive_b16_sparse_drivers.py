"""Instantiate the proven generic matching/control workflow for B16."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    reportpath = ROOT / "b16-sparse-driver-derivation.json"
    assert not reportpath.exists()
    records = []
    for original, target, changes in (
        ("test_generic_sparse_collar.py", "test_b16_sparse_collar.py", [
            ("assert B == 15", "assert B == 16"),
            ("for N in range(B+4, B+9):", "for N in (B+1, B+2, B+3, B+6, B+7):"),
            ("B15", "B16"),
        ]),
        ("run_family_sparse_collar.py", "run_b16_sparse_collar.py", [
            ("assert B == 15", "assert B == 16"),
            ('"test_generic_sparse_collar.py"', '"test_b16_sparse_collar.py"'),
            ("N25/B15", "N25/B16"),
        ]),
    ):
        sourcepath, targetpath = ROOT / original, ROOT / target
        assert not targetpath.exists()
        old = sourcepath.read_text(encoding="utf8")
        new = old
        for before, after in changes:
            assert before in new and after not in new
            new = new.replace(before, after)
        targetpath.write_text(new, encoding="utf8", newline="\n")
        records.append({
            "original": original, "derived": target,
            "original_sha256": sha(sourcepath), "derived_sha256": sha(targetpath),
            "changes": changes,
        })
    reportpath.write_text(json.dumps({
        "records": records, "source_sha256": sha(Path(__file__)),
        "boundary_instantiation_and_test_sizes_only": True,
        "native_recursion_and_mathematical_acceptance_unchanged": True,
        "global_optimality_proved": False,
    }, indent=2)+"\n", encoding="utf8")


if __name__ == "__main__":
    main()
