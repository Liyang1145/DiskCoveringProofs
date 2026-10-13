"""Mechanically generalize new standalone B14 tools, without editing any pins."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    reportpath = ROOT / "family-discovery-tool-derivation.json"
    assert not reportpath.exists()
    records = []
    routes = (
        ("catalog_collar_discovery.py", "catalog_family_discovery.py", "data"),
        ("probe_collar_discovery.py", "probe_family_discovery.py", "data"),
        ("replay_collar_discovery.py", "replay_family_discovery.py", "snapshot"),
        ("sparsify_discovery_graphs.py", "sparsify_family_discovery.py", "snapshot"),
        ("export_sparse_outer_library.py", "export_family_sparse_library.py", "groups"),
    )
    renames = {
        '"probe_collar_discovery.py"': '"probe_family_discovery.py"',
        '"replay_collar_discovery.py"': '"replay_family_discovery.py"',
    }
    for original, target, owner in routes:
        sourcepath, targetpath = ROOT / original, ROOT / target
        old = sourcepath.read_text(encoding="utf8")
        new = re.sub(r"\b14\b", "B", old)
        for before, after in renames.items():
            new = new.replace(before, after)
        assertion_owner = "receipt" if owner == "snapshot" else owner
        first = "    assert (groups[" if owner == "groups" else f"    assert {assertion_owner}["
        position = new.index(first)
        declaration = f'    B = {owner}["B"]\n    assert B in (14, 15, 16, 17)\n'
        new = new[:position]+declaration+new[position:]
        if owner == "snapshot":
            new = new.replace(
                f'    B = {owner}["B"]\n',
                f'    B = {owner}["B"]\n    assert receipt["B"] == B\n', 1)
        if targetpath.exists():
            assert targetpath.read_text(encoding="utf8") == new
        else:
            targetpath.write_text(new, encoding="utf8", newline="\n")
        records.append({
            "original": original, "derived": target, "original_sha256": sha(sourcepath),
            "derived_sha256": sha(targetpath),
            "boundary_literal_replaced_by_snapshot_B": True,
            "boundary_family_range_explicitly_checked": True,
            "only_boundary_parameter_and_corresponding_source_names_changed": True,
        })
    reportpath.write_text(json.dumps({
        "schema": "generic-n25-discovery-tool-derivation-v1", "records": records,
        "source_sha256": sha(Path(__file__)),
        "does_not_certify_a_complete_family": True, "global_optimality_proved": False,
    }, indent=2)+"\n", encoding="utf8")


if __name__ == "__main__":
    main()
