"""Mechanically derive a bounded discovery snapshot, never a complete catalog.

The frozen production source is not edited. The only substitution changes its
entry-point name. After its fail-closed bounded run returns, a separate wrapper
exports the in-memory proposals under an explicitly incomplete schema.
"""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    source = ROOT / "peel_sparse_outer_collar.cpp"
    bodypath = ROOT / "collar_discovery_body.inc"
    reportpath = ROOT / "collar-discovery-source-derivation.json"
    assert not bodypath.exists() and not reportpath.exists()
    old = source.read_text(encoding="utf8")
    before = "int main(int argc,char**argv){try{"
    after = "int bounded_production_entry(int argc,char**argv){try{"
    assert old.count(before) == 1 and after not in old
    new = old.replace(before, after, 1)
    assert new.replace(after, before, 1) == old
    bodypath.write_text(new, encoding="utf8", newline="\n")
    reportpath.write_text(json.dumps({
        "schema": "bounded-collar-discovery-source-derivation-v1",
        "production_source_sha256": sha(source),
        "derived_body_sha256": sha(bodypath),
        "only_entry_point_name_changed": True,
        "recursive_search_and_guards_unchanged": True,
        "snapshots_are_incomplete_discovery_proposals_only": True,
        "source_sha256": sha(Path(__file__)),
        "global_optimality_proved": False,
    }, indent=2)+"\n", encoding="utf8")


if __name__ == "__main__":
    main()
