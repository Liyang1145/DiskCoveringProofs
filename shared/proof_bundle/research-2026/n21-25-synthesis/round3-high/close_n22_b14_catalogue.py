"""Close the n22 B14 recorded catalogue with one explicit attaining core case.

The result is a branch theorem: all other recorded types are excluded and
the sole attaining type is paid by the positive-core lower-bound tree.
Actual-cover reduction, catalogue completeness, and B13/B15 remain separate.
"""
from pathlib import Path
import argparse
import json
from fractions import Fraction as F
from stream_catalog import sha, no_duplicate_keys

ROOT = Path(__file__).resolve().parent
assert __debug__


def read(path):
    return json.loads(Path(path).read_text(encoding="utf8"), object_pairs_hook=no_duplicate_keys)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--hierarchy", type=Path, required=True)
    ap.add_argument("--force-replay", type=Path, required=True)
    ap.add_argument("--core", type=Path, required=True)
    ap.add_argument("--interfaces", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    auditpath = args.hierarchy
    audit = read(auditpath)
    pendingpath = auditpath.parent / audit["pending_indices_file"]
    pending = [json.loads(line)["index"] for line in pendingpath.open(encoding="utf8")]
    assert audit["verified"] and audit["disjoint_hierarchy_partition_verified"]
    assert audit["N"] == 22 and audit["B"] == 14
    assert audit["catalog_types"] == 3080858
    assert audit["strict_exclusion_types_with_replayed_certificates"] == 3080857
    assert audit["pending_types"] == 1 and pending == [3080857]
    assert sha(pendingpath) == audit["pending_indices_sha256"]
    assert audit["source_sha256"] == sha(ROOT / "audit_streamed_hierarchy.py")
    assert audit["stream_reader_sha256"] == sha(ROOT / "stream_catalog.py")
    force = read(args.force_replay)
    assert force["verified"] and (force["N"], force["B"]) == (22, 14)
    assert force["source_sha256"] == sha(ROOT / "replay_group_stage.py")
    assert force["exact_checker_sha256"] == sha(ROOT / "exact_graph.py")
    assert force["exact_groups_replayed"] == 384769 and force["pending_groups"] == 1
    assert force["associated_member_count"] == 384769
    assert force["groups_sha256"] == audit["stages"][-1]["groups_sha256"]
    assert force["bindings_sha256"] == audit["stages"][-1]["bindings_sha256"]
    assert audit["stages"][-1]["force_replay_sha256"] == sha(args.force_replay)
    assert F(force["minimum_force_margin"]) > 0
    core = read(args.core)
    assert core["verified"] and core["catalog_index"] == pending[0]
    assert core["full_group"] == 384769
    assert core["scope"].startswith("one explicitly mapped full-type core lower bound")
    assert core["groups_sha256"] == force["groups_sha256"]
    assert core["bindings_sha256"] == force["bindings_sha256"]
    assert core["catalog_sha256"] == audit["catalog_sha256"]
    assert core["source_sha256"] == sha(ROOT / "n22_core_case.py")
    assert core["transfer_checker_sha256"] == sha(ROOT / "audit_streamed_hierarchy.py")
    assert core["exact_checker_sha256"] == sha(ROOT / "exact_graph.py")
    assert core["force_kernel_sha256"] == sha(ROOT.parent / "round2-grouped/partial_force_exact.py")
    assert core["tree_sha256"] == sha(ROOT / "evidence/n22-core-angle-resume2/core-angle-tree.json.gz")
    # Exact links to the independent root/system/local inputs.
    assert core["root_sha256"] == sha(ROOT.parent / "evidence/n22/core-root.json")
    assert core["system_sha256"] == sha(ROOT.parent / "evidence/n22/core-system.json")
    assert core["local_certificate_sha256"] == sha(ROOT.parent / "evidence/n22/local-isolation-certificate.json")
    assert core["constants_sha256"] == sha(ROOT.parent / "evidence/core-reduction/constants/n22.json")
    assert F(core["minimum_force_margin"]) > 0
    assert F(core["minimum_local_margin"]) > 0
    interfaces = read(args.interfaces)
    assert interfaces["verified"] and interfaces["N"] == 22
    assert interfaces["same_root_entire_closed_disk_upper"]
    assert interfaces["root_and_geometric_isolation_freshly_replayed"]
    assert interfaces["root_sha256"] == core["root_sha256"]
    assert interfaces["system_sha256"] == core["system_sha256"]
    assert interfaces["local_certificate_sha256"] == core["local_certificate_sha256"]
    interfacefolder = args.interfaces.parent / "evidence/n22"
    assert interfaces["root_report_sha256"] == sha(interfacefolder / "algebraic-check1/root-verified.json")
    assert interfaces["upper_report_sha256"] == sha(interfacefolder / "algebraic-check1/upper-verified.json")
    assert interfaces["local_certificate_sha256"] == sha(interfacefolder / "local-isolation-certificate.json")
    assert interfaces["source_sha256"] == sha(ROOT / "replay_n22_interfaces.py")
    assert interfaces["root_acceptor_sha256"] == sha(ROOT.parent / "algebraic_roots.py")
    assert interfaces["local_acceptor_sha256"] == sha(ROOT.parent / "local_certificates.py")
    candidate = read(ROOT / "evidence/n22-symmetry-cubic-replay-resume1.json")
    assert candidate["verified"] and candidate["candidate_symmetry_D7_certified"]
    assert candidate["linked_radius_square_polynomial_ascending"] == [-1, 19, -55, 29]
    assert candidate["root_sha256"] == core["root_sha256"]
    assert candidate["system_sha256"] == core["system_sha256"]
    assert candidate["source_sha256"] == sha(ROOT / "n22_symmetry_link.py")
    report = {"verified": True, "N": 22, "B": 14,
              "catalog_types": 3080858,
              "strict_exclusion_types": 3080857,
              "attaining_core_types": 1,
              "pending_catalog_indices": [],
              "core_paid_catalog_indices": pending,
              "attaining_catalog_index": core["catalog_index"],
              "attaining_group": core["full_group"],
              "all_nonattaining_recorded_types_excluded": True,
              "attaining_type_core_lower_bound_replayed": True,
              "radius_link_report_sha256": sha(ROOT / "evidence/n22-symmetry-cubic-replay-resume1.json"),
              "hierarchy_audit_sha256": sha(auditpath),
              "pending_indices_sha256": sha(pendingpath),
              "core_case_sha256": sha(args.core),
              "full_force_replay_sha256": sha(args.force_replay),
              "fresh_interfaces_sha256": sha(args.interfaces),
              "all_components_hash_bound": True,
              "scope": "complete B14 recorded catalogue branch; not whole n22 theorem",
              "catalog_completeness_proved_here": False,
              "actual_cover_reduction_proved_here": False,
              "global_optimality_proved": False,
              "source_sha256": sha(Path(__file__))}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2), encoding="utf8")
    print("N22 B14 recorded branch closure PASS: 3080857 excluded + one attaining core case", flush=True)


if __name__ == "__main__":
    main()
