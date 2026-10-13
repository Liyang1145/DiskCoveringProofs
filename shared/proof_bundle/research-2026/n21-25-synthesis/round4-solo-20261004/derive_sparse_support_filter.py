"""New-file-only necessary support filters; frozen search code remains intact."""
from pathlib import Path
import json
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "round3-high"))
from stream_catalog import sha

assert __debug__


def derive(source, target, changes):
    source_path, target_path = ROOT / source, ROOT / target
    assert not target_path.exists()
    before = source_path.read_text(encoding="utf8")
    text = before
    for old, new in changes:
        assert text.count(old) == 1, (source, old, text.count(old))
        text = text.replace(old, new)
    reverse = text
    for old, new in reversed(changes):
        assert reverse.count(new) == 1
        reverse = reverse.replace(new, old)
    assert reverse == before
    target_path.write_text(text, encoding="utf8", newline="\n")
    return {"source": source, "source_sha256": sha(source_path),
            "target": target, "target_sha256": sha(target_path),
            "changes": changes, "exact_inverse_equals_frozen_source": True}


def main():
    report_path = ROOT / "sparse-support-filter-source-derivation.json"
    assert not report_path.exists()
    changes = [
        (" int id,K,shift,sign;\n",
         " int id,K,shift,sign;\n int required_faces=0;\n"
         " array<int,4> required_boundary_type_counts{};\n"
         " uint32_t required_boundary_support=0;\n"),
        ("   SparseVariant v;v.id=pattern.id;v.K=K;v.shift=shift;v.sign=sign;\n",
         "   SparseVariant v;v.id=pattern.id;v.K=K;v.shift=shift;v.sign=sign;\n"
         "   v.required_faces=pattern.faces.size();\n"),
        ("    if(interior.empty())v.all_boundary_faces.push_back(boundary);\n",
         "    v.required_boundary_support|=boundary;\n"
         "    v.required_boundary_type_counts[pop(boundary)]++;\n"
         "    if(interior.empty())v.all_boundary_faces.push_back(boundary);\n"),
        (" uint32_t used_inside=0,bmask=(uint32_t(1)<<b)-1;\n",
         " uint32_t used_inside=0,bmask=(uint32_t(1)<<b)-1;\n"
         " uint32_t target_boundary_support=0;\n array<int,4> target_boundary_type_counts{};\n"),
        ("  uint32_t boundary=face&bmask,inside=face^boundary;\n",
         "  uint32_t boundary=face&bmask,inside=face^boundary;\n"
         "  target_boundary_support|=boundary;\n target_boundary_type_counts[pop(boundary)]++;\n"),
        (" for(auto const& variant:sparse_variants){\n  int K=variant.K;\n",
         " for(auto const& variant:sparse_variants){\n"
         "  if(variant.required_faces>(int)raw.size()||\n"
         "     (variant.required_boundary_support&~target_boundary_support))continue;\n"
         "  bool type_counts_fit=true;\n"
         "  for(int type=1;type<=3;type++)\n"
         "   if(variant.required_boundary_type_counts[type]>target_boundary_type_counts[type])\n"
         "    {type_counts_fit=false;break;}\n"
         "  if(!type_counts_fit)continue;\n"
         "  int K=variant.K;\n"),
    ]
    records = [derive("sparse_outer_matcher.inc", "sparse_support_matcher.inc", changes)]
    for source, target in (
        ("sparse_outer_match.cpp", "sparse_support_match.cpp"),
        ("peel_eight_rod_collar.cpp", "peel_support_eight_collar.cpp"),
        ("peel_origin_streamed_collar.cpp", "peel_support_origin_collar.cpp"),
    ):
        records.append(derive(source, target, [
            ('#include "sparse_outer_matcher.inc"', '#include "sparse_support_matcher.inc"')
        ]))
    report_path.write_text(json.dumps({
        "verified": True, "schema": "necessary-sparse-support-filter-derivation-v1",
        "source_sha256": sha(Path(__file__)), "files": records,
        "only_necessary_matching_filters_and_include_names_changed": True,
        "all_existing_candidate_search_and_positive_injection_checks_unchanged": True,
        "full_search_recursion_angles_storage_and_origin_condition_unchanged": True,
        "source_lemma_sha256": sha(ROOT / "SPARSE-SUPPORT-NECESSARY-FILTERS.md"),
        "global_optimality_proved": False,
    }, indent=2)+"\n", encoding="utf8")
    print("Necessary sparse support filters and three isolated native sources derived", flush=True)


if __name__ == "__main__":
    main()
