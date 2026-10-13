"""Derive a separate equal-outer-face matcher for fixed N25 completion theorems."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def derive(text):
    names = sorted(set(re.findall(r"\b[A-Za-z_][A-Za-z_0-9]*\b", text)))
    renames = {}
    for name in names:
        if "sparse" in name:
            renames[name] = name.replace("sparse", "completion")
        elif "Sparse" in name:
            renames[name] = name.replace("Sparse", "Completion")
    new = re.sub(r"\b[A-Za-z_][A-Za-z_0-9]*\b", lambda m: renames.get(m.group(), m.group()), text)
    changes = [
        ('"strict-completion-outer-obstacle-library-v1"', '"paid-simple-collar-completion-library-v1"'),
        ('if(path=="-")return;\n', 'if(path=="-")return;\n if(n!=25)throw runtime_error("completion theorem requires exactly N25");\n'),
        ('int id,K,shift,sign;', 'int id,K,shift,sign,F;'),
        ('v.id=pattern.id;v.K=K;v.shift=shift;v.sign=sign;',
         'v.id=pattern.id;v.K=K;v.shift=shift;v.sign=sign;v.F=pattern.faces.size();'),
        ('(used|((uint32_t(1)<<B)-1))!=(uint32_t(1)<<N)-1',
         'used!=(uint32_t(1)<<N)-1'),
        ('if(K>pop(used_inside))continue;',
         'if(K!=pop(used_inside)||(int)raw.size()!=variant.F)continue;'),
        ('if((int)match.centers.size()!=pattern.centers||(int)match.anchors.size()!=b)',
         'if(raw.size()!=pattern.faces.size()||(int)match.centers.size()!=pattern.centers||(int)match.anchors.size()!=b)'),
    ]
    for before, after in changes:
        assert new.count(before) == 1
        new = new.replace(before, after, 1)
    # Source recursion/filters are unchanged except the exact F/K and domain gates.
    reconstructed = new
    for before, after in reversed(changes):
        assert reconstructed.count(after) == 1
        reconstructed = reconstructed.replace(after, before, 1)
    inverse = {newname: oldname for oldname, newname in renames.items()}
    reconstructed = re.sub(r"\b[A-Za-z_][A-Za-z_0-9]*\b",
                           lambda m: inverse.get(m.group(), m.group()), reconstructed)
    assert reconstructed == text
    return new, renames, changes


def main():
    original = ROOT / "sparse_outer_matcher.inc"
    target = ROOT / "completion_family_matcher.inc"
    reportpath = ROOT / "completion-matcher-source-derivation.json"
    assert not target.exists() and not reportpath.exists()
    text = original.read_text(encoding="utf8")
    new, names, changes = derive(text)
    target.write_text(new, encoding="utf8", newline="\n")
    reportpath.write_text(json.dumps({
        "verified_mechanical_derivation": True,
        "original_matcher_sha256": sha(original), "derived_matcher_sha256": sha(target),
        "identifier_renames": names, "explicit_changes": changes,
        "exact_N25_and_equal_outer_face_cardinality_required": True,
        "all_successful_center_anchor_face_injections_still_rechecked": True,
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False,
    }, indent=2)+"\n", encoding="utf8")


if __name__ == "__main__":
    main()
