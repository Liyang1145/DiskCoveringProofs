"""Keep all slab union checks; accept only the new explicitly qualified schema."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    original, target = ROOT / "merge_collar_chunks.py", ROOT / "merge_origin_collar_chunks.py"
    reportpath = ROOT / "origin-chunk-merge-source-derivation.json"
    assert not target.exists() and not reportpath.exists()
    text = original.read_text(encoding="utf8")
    before = '    assert manifest["schema"] == "complete-outer-collar-sorted-chunks-v1"'
    after = '''    assert manifest["schema"] == "complete-cover-origin-collar-sorted-chunks-v1"
    assert manifest["origin_cover_only_N25"]
    assert manifest["origin_cover_scope"] == "actual arbitrary disk covers only; not weak graph geometry"
    assert manifest["origin_radius_upper_numerator"] == 239146311738101
    assert manifest["origin_radius_upper_denominator"] == 10**15
    assert 4*manifest["origin_radius_upper_numerator"] < manifest["origin_radius_upper_denominator"]
    for sample in manifest["origin_cover_samples"]:
        mask = (1 << manifest["B"])-1
        for face in sample["outer_faces"]:
            assert type(face) is int and 0 < face < 1 << 25 and face.bit_count() == 3
            assert face & ((1 << manifest["B"])-1)
            mask |= face
        assert mask == (1 << 25)-1
    if manifest["N"] != 25 or not manifest["origin_cover_screen"]:
        assert manifest["origin_cover_prunes_not_type_count"] == 0
        assert not manifest["origin_cover_samples"]'''
    changes = [(before, after),
               ('                assert B <= centers <= N and faces and faces == sorted(set(faces))',
                '''                maximum = N-1 if N == 25 and manifest["origin_cover_screen"] else N
                assert B <= centers <= maximum and faces and faces == sorted(set(faces))''')]
    for old, new in changes:
        assert text.count(old) == 1
        text = text.replace(old, new)
    target.write_text(text, encoding="utf8", newline="\n")
    reportpath.write_text(json.dumps({
        "verified_mechanical_derivation": True, "original_source_sha256": sha(original),
        "derived_source_sha256": sha(target), "source_sha256": sha(Path(__file__)),
        "changes": changes, "all_old_complete_zero_exit_slab_union_checks_preserved": True,
        "new_origin_schema_and_explicit_samples_checked": True,
        "global_optimality_proved": False,
    }, indent=2)+"\n", encoding="utf8")


if __name__ == "__main__":
    main()
