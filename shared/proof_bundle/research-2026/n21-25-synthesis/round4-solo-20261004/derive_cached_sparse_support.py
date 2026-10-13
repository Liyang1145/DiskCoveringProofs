"""Cache necessary filter candidates in new files, preserving match order."""
from pathlib import Path
import json
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "round3-high"))
from stream_catalog import sha
from n25_outer_search import read, publish, unchanged
from support_filter_gate import derivation_gate
from derive_sparse_support_filter import derive

assert __debug__


def main():
    files = derivation_gate()
    report_path = ROOT / "cached-sparse-support-source-derivation.json"
    assert not report_path.exists()
    old_loop = (
        " for(auto const& variant:sparse_variants){\n"
        "  if(variant.required_faces>(int)raw.size()||\n"
        "     (variant.required_boundary_support&~target_boundary_support))continue;\n"
        "  bool type_counts_fit=true;\n"
        "  for(int type=1;type<=3;type++)\n"
        "   if(variant.required_boundary_type_counts[type]>target_boundary_type_counts[type])\n"
        "    {type_counts_fit=false;break;}\n"
        "  if(!type_counts_fit)continue;\n"
        "  int K=variant.K;\n")
    new_loop = (
        " array<uint32_t,7> support_key{uint32_t(n),uint32_t(b),target_boundary_support,\n"
        "  uint32_t(raw.size()),uint32_t(target_boundary_type_counts[1]),\n"
        "  uint32_t(target_boundary_type_counts[2]),uint32_t(target_boundary_type_counts[3])};\n"
        " vector<size_t> uncached_support_candidates;\n"
        " vector<size_t> const* selected_support_candidates=nullptr;\n"
        " auto support_entry=sparse_support_candidates.find(support_key);\n"
        " if(support_entry==sparse_support_candidates.end()){\n"
        "  vector<size_t> candidates;\n"
        "  for(size_t variant_index=0;variant_index<sparse_variants.size();variant_index++){\n"
        "   auto const& variant=sparse_variants[variant_index];\n"
        "   if(variant.required_faces>(int)raw.size()||\n"
        "      (variant.required_boundary_support&~target_boundary_support))continue;\n"
        "   bool type_counts_fit=true;\n"
        "   for(int type=1;type<=3;type++)\n"
        "    if(variant.required_boundary_type_counts[type]>target_boundary_type_counts[type])\n"
        "     {type_counts_fit=false;break;}\n"
        "   if(type_counts_fit)candidates.push_back(variant_index);\n"
        "  }\n"
        "  if(candidates.size()>1048576){\n"
        "   uncached_support_candidates=move(candidates);\n"
        "   selected_support_candidates=&uncached_support_candidates;\n"
        "  }else{\n"
        "   if(sparse_support_candidates.size()>=4096||\n"
        "      sparse_support_candidate_entries+candidates.size()>1048576){\n"
        "    sparse_support_candidates.clear();sparse_support_candidate_entries=0;\n"
        "   }\n"
        "   sparse_support_candidate_entries+=candidates.size();\n"
        "   support_entry=sparse_support_candidates.emplace(support_key,move(candidates)).first;\n"
        "  }\n"
        " }\n"
        " if(!selected_support_candidates)selected_support_candidates=&support_entry->second;\n"
        " for(size_t variant_index:*selected_support_candidates){\n"
        "  auto const& variant=sparse_variants[variant_index];\n"
        "  int K=variant.K;\n")
    records = [derive("sparse_support_matcher.inc", "sparse_support_cached_matcher.inc", [
        ("vector<SparseVariant> sparse_variants;\n",
         "vector<SparseVariant> sparse_variants;\n"
         "map<array<uint32_t,7>,vector<size_t>> sparse_support_candidates;\n"
         "uint64_t sparse_support_candidate_entries=0;\n"),
        (old_loop, new_loop),
    ])]
    for source, target in (
        ("sparse_support_match.cpp", "sparse_support_cached_match.cpp"),
        ("peel_support_eight_collar.cpp", "peel_cached_support_eight_collar.cpp"),
        ("peel_support_origin_collar.cpp", "peel_cached_support_origin_collar.cpp"),
    ):
        records.append(derive(source, target, [
            ('#include "sparse_support_matcher.inc"', '#include "sparse_support_cached_matcher.inc"')
        ]))
    unchanged(files)
    publish(report_path, {
        "verified": True, "schema": "bounded-sparse-support-cache-derivation-v1",
        "source_sha256": sha(Path(__file__)), "files": records,
        "prior_derivation_sha256": sha(ROOT / "sparse-support-filter-source-derivation.json"),
        "source_lemma_sha256": sha(ROOT / "SPARSE-SUPPORT-CACHE-SOURCE.md"),
        "complete_integer_key_contains_all_filter_target_values": True,
        "original_variant_and_internal_search_order_preserved": True,
        "all_positive_checks_and_recursion_unchanged": True,
        "maximum_cached_keys": 4096, "maximum_cached_candidate_indices": 1048576,
        "cache_eviction_not_a_recursion_prune": True,
        "global_optimality_proved": False,
    })
    print("Bounded support-candidate cache derived, with exact inverse and original match order", flush=True)


if __name__ == "__main__":
    main()
