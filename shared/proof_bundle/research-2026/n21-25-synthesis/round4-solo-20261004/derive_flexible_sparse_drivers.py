"""Derive fresh drivers with an explicit matching-controls path.

Only the CLI, controls-file path, and new controls-source name change. The
native source/binary, library exact gate, full-catalog acceptance, and source
induction remain unchanged. Original running drivers are never edited.
"""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    reportpath = ROOT / "flexible-sparse-driver-derivation.json"
    assert not reportpath.exists()
    records = []
    oldpath = 'ROOT / "n25-B14-sparse-match-controls-v1/VERIFIED.json"'
    insertion = '    args = ap.parse_args()'
    new_cli = '    ap.add_argument("--maps", type=Path, required=True)\n'+insertion
    for original, target, controls_name in (
        ("test_sparse_collar.py", "test_sparse_collar_flexible.py", False),
        ("run_sparse_collar.py", "run_sparse_collar_flexible.py", True),
    ):
        sourcepath, targetpath = ROOT / original, ROOT / target
        assert not targetpath.exists()
        before = sourcepath.read_text(encoding="utf8")
        changes = [(insertion, new_cli), (oldpath, "args.maps.resolve()")]
        if controls_name:
            changes.append(('"test_sparse_collar.py"', '"test_sparse_collar_flexible.py"'))
        after = before
        counts = []
        for old, new in changes:
            count = after.count(old)
            assert count > 0 and new not in after
            if old == insertion:
                assert count == 1
            after = after.replace(old, new)
            counts.append(count)
        reconstructed = after
        for old, new in reversed(changes):
            reconstructed = reconstructed.replace(new, old)
        assert reconstructed == before
        targetpath.write_text(after, encoding="utf8", newline="\n")
        records.append({
            "original": original, "derived": target, "original_sha256": sha(sourcepath),
            "derived_sha256": sha(targetpath), "changes": changes, "occurrence_counts": counts,
        })
    reportpath.write_text(json.dumps({
        "verified_mechanical_derivation": True,
        "records": records, "source_sha256": sha(Path(__file__)),
        "original_driver_and_native_files_not_modified": True,
        "mathematical_acceptance_logic_not_changed": True,
        "global_optimality_proved": False,
    }, indent=2)+"\n", encoding="utf8")


if __name__ == "__main__":
    main()
