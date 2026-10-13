"""Stdlib-only all-parent B14 payment audit; any missing certificate remains unpaid."""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
import argparse
import gzip
import json
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
import exact_graph as exact
from stream_catalog import sha, no_duplicate_keys
from group_catalog import canonical, validate
from n25_outer_search import read, publish, bind, unchanged, WORK
from run_sparse_collar import sparse_library_gate
from test_sparse_collar import mechanical_derivation
from verify_sparse_maps_fast import library_gate
from completion_family_gate import validate_outer_payment
from batch_streamed_collar import identity
from eight_rod_angles import constants_gate, verify_cycle
from refine_collar_origin import exposed_mask, radius_gate
from proof_paid_hole_kernel import replay as simple_replay
from linked_general_collar_kernel import replay as general_replay
from test_linked_general_collar import derivation_gate as general_derivation

assert __debug__


def ledger(path, groups, field="parent_group"):
    result, previous = {}, -1
    with path.open(encoding="ascii") as stream:
        for line in stream:
            row = json.loads(line, object_pairs_hook=no_duplicate_keys)
            gid = row[field]
            assert type(gid) is int and previous < gid < len(groups)
            assert gid not in result
            previous = gid
            result[gid] = row
    return result


def residual(path, groups, expected_header):
    result, previous = {}, -1
    with path.open(encoding="ascii") as stream:
        header = json.loads(next(stream), object_pairs_hook=no_duplicate_keys)
        for key, value in expected_header.items():
            assert header[key] == value
        for line in stream:
            row = json.loads(line, object_pairs_hook=no_duplicate_keys)
            gid = row["id"]
            assert previous < gid < len(groups) and row == groups[gid]
            previous = gid
            result[gid] = row
    return result


def check_partition(parent, paid, remaining):
    assert set(paid).isdisjoint(remaining)
    assert set(paid) | set(remaining) == set(parent), "payment/residual partition has a gap or extra parent"


def same_branch_result(result, accepted):
    for key, value in result.items():
        assert accepted[key] == value, ("branch replay receipt differs from fresh mathematics", key)


def main():
    ap = argparse.ArgumentParser()
    for name in ("base", "postfilter", "origin", "force", "simple", "pinched", "fixed-branches", "output"):
        ap.add_argument("--"+name, type=Path, required=True)
    ap.add_argument("--refinement-exact", type=Path, action="append", default=[])
    args = ap.parse_args()
    base, postfilter, origin, force, simple, pinched, output = (
        getattr(args, name).resolve() for name in ("base", "postfilter", "origin", "force", "simple", "pinched", "output"))
    assert output.is_relative_to(ROOT) and not output.exists()
    fixed_branches = args.fixed_branches.resolve()
    files = {}
    constants_path = HIGH.parent / "evidence/core-reduction/constants/n25.json"
    constants = read(constants_path)
    constants_digest = sha(constants_path)
    U = F(constants["radius_upper"])
    assert constants["verified"] and constants["N"] == 25
    assert U == F(239146311738101, 10**15) and constants["families"] == [[b, 25-b] for b in range(14, 18)]
    constants_gate(constants)
    gap = radius_gate(U)
    alpha = F(3, 2)*(1-U*U)
    assert 0 < alpha and alpha*alpha < 2
    mechanical_derivation()
    _, old_library, _, old_files = sparse_library_gate(ROOT / "n25-B14-sparse-library-v1/LIBRARY.json")
    _, strict_library, _, strict_files = library_gate(ROOT / "n25-B14-union-sparse-library-20261005-v1/LIBRARY.json")
    files.update(old_files);files.update(strict_files)
    general_derivation()
    summary, terminal, input_bindings = map(read, (base / "SUMMARY.json", base / "NATIVE-TERMINAL.json",
                                                  base / "INPUT-BINDINGS.json"))
    assert summary["verified"] and summary["complete_necessary_outer_collar_overapproximation"]
    assert summary["source_sha256"] == sha(ROOT / "run_sparse_collar.py")
    assert terminal["native_terminal_observed"] and terminal["actual_exit_code"] == 0
    assert terminal["native_log_sha256"] == sha(base / "NATIVE-STDERR.log")
    assert (summary["N"], summary["B"]) == (input_bindings["N"], input_bindings["B"]) == (25, 14)
    unchanged(summary["files_relative_to_workspace"])
    unchanged(input_bindings["files_relative_to_workspace"])
    files.update(summary["files_relative_to_workspace"])
    catalogpath = base / "N25-B14-necessary-sparse-collars.json"
    assert sha(catalogpath) == summary["native_catalog_sha256"]
    native = read(catalogpath)
    assert native["complete_necessary_outer_search"] and not native["complete_full_triangulations"]
    assert native["schema"] == "outer-collar-overapproximation-v1"
    assert (native["N"], native["B"], native["mode"], native["screen"]) == (25, 14, "dfs", True)
    assert native["scale"] == constants["angle_scale"] and native["caps"] == constants["angle_caps"]
    assert native["sparse_patterns_loaded"] == old_library["obstacle_count"] and native["paid_patterns_loaded"] == 0
    command = input_bindings["command"]
    assert command[-3] == "dfs" and command[-4] == "0"
    for payment in native["sparse_payments"]:
        obstacle = old_library["obstacles"][payment["obstacle"]]
        validate(25, 14, obstacle["faces"],
                 {key: payment[key] for key in ("centers", "anchors", "orientation", "shift")},
                 payment["sample_faces"])
    groupspath = base / "GROUPS.json"
    groups_digest = sha(groupspath)
    assert groups_digest == summary["groups_sha256"]
    data = read(groupspath)
    groups = data["groups"]
    total = data["group_count"]
    assert (data["N"], data["B"], data["threshold"]) == (25, 14, 1)
    assert len(groups) == len(native["weak_graphs"]) == total == native["weak_graph_count"] == summary["unpaid_weak_graphs"]
    assert data["full_selected_catalog_scanned"] and data["verified_embeddings_during_generation"]
    assert data["members_are_necessary_weak_graphs_not_full_types"]
    bindingpath = base / data["bindings_file"]
    assert sha(bindingpath) == data["bindings_sha256"]
    previous = None
    with bindingpath.open(encoding="ascii") as bindings:
        for gid, (group, raw) in enumerate(zip(groups, native["weak_graphs"], strict=True)):
            assert group == {"id": gid, **raw, "members": 1}
            centers, faces = group["centers"], group["faces"]
            assert type(centers) is int and 14 <= centers <= 25
            assert faces and faces == sorted(set(faces))
            assert exposed_mask(centers, 14, faces) == (1 << centers)-1
            assert all(mask & ((1 << 14)-1) for mask in faces)
            used = 0
            for face in faces:
                used |= face
            assert used == (1 << centers)-1
            code = tuple(faces)
            assert previous is None or previous < code
            previous = code
            binding = json.loads(next(bindings), object_pairs_hook=no_duplicate_keys)
            assert binding == {"index": gid, "group": gid, "map": identity(centers, 14)}
        assert not bindings.read().strip()
    # Every completed chain is rechecked by per-id disjoint set equalities.
    post = read(postfilter / "VERIFIED.json")
    origin_report = read(origin / "VERIFIED.json")
    force_report = read(force / "VERIFIED.json")
    for report, source in ((post, "filter_complete_collar_cached.py"),
                            (origin_report, "refine_collar_origin.py"), (force_report, "pay_origin_refined_force.py")):
        assert report["verified"] and (report["N"], report["B"]) == (25, 14)
        assert report["source_sha256"] == sha(ROOT / source)
        unchanged(report["files_relative_to_workspace"])
    assert post["schema"] == "complete-old-collar-independent-paid-partition-v1"
    assert post["all_complete_parent_rows_processed_once"] and post["parent_groups_sha256"] == sha(groupspath)
    assert sha(postfilter / "PAYMENTS.jsonl") == post["payments_sha256"]
    assert sha(postfilter / "RESIDUAL.jsonl") == post["residual_sha256"]
    post_paid = ledger(postfilter / "PAYMENTS.jsonl", groups)
    post_remaining = residual(postfilter / "RESIDUAL.jsonl", groups, {
        "schema": "complete-paid-old-collar-residual-v1", "N": 25, "B": 14,
        "source_catalog_sha256": sha(groupspath)})
    check_partition(range(total), post_paid, post_remaining)
    assert Counter(p["kind"] for p in post_paid.values()) == {
        k: v for k, v in post["payment_counts"].items() if k != "unpaid"}
    assert len(post_remaining) == post["residual_weak_graphs"]
    assert origin_report["schema"] == "complete-collar-actual-cover-origin-refinement-v1"
    assert origin_report["parent_report_sha256"] == sha(postfilter / "VERIFIED.json")
    assert origin_report["parent_residual_sha256"] == sha(postfilter / "RESIDUAL.jsonl")
    assert sha(origin / "ORIGIN-PAYMENTS.jsonl") == origin_report["origin_payments_sha256"]
    assert sha(origin / "RESIDUAL.jsonl") == origin_report["refined_residual_sha256"]
    origin_paid = ledger(origin / "ORIGIN-PAYMENTS.jsonl", groups)
    origin_remaining = residual(origin / "RESIDUAL.jsonl", groups, {
        "schema": "complete-collar-origin-refined-residual-v1", "N": 25, "B": 14,
        "source_catalog_sha256": sha(groupspath)})
    check_partition(post_remaining, origin_paid, origin_remaining)
    assert len(origin_paid) == origin_report["origin_obstruction_paid"]
    assert len(origin_remaining) == origin_report["remaining_weak_graphs"]
    for gid, payment in origin_paid.items():
        assert payment["kind"] == "actual-cover-origin-unexposed-center-obstruction"
        assert F(payment["radius_upper"]) == U and F(payment["strict_gap_1_minus_4U"]) == gap
        assert groups[gid]["centers"] == 25
    assert force_report["schema"] == "complete-origin-residual-exact-force-refinement-v1"
    assert force_report["parent_refined_report_sha256"] == sha(origin / "VERIFIED.json")
    assert force_report["parent_catalog_sha256"] == sha(groupspath)
    assert sha(force / "PAYMENTS.jsonl") == force_report["payments_sha256"]
    assert sha(force / "RESIDUAL.jsonl") == force_report["residual_sha256"]
    force_paid = ledger(force / "PAYMENTS.jsonl", groups)
    last_remaining = residual(force / "RESIDUAL.jsonl", groups, {
        "schema": "complete-collar-origin-and-exact-force-residual-v1", "N": 25, "B": 14,
        "source_catalog_sha256": sha(groupspath)})
    check_partition(origin_remaining, force_paid, last_remaining)
    assert len(last_remaining) == force_report["remaining_weak_graphs"]
    # Prior fixed-family payments are paid again through small complete
    # branch trees. This audit does not rely on a closure status flag alone.
    fixed_summary = read(fixed_branches / "SUMMARY.json")
    assert fixed_summary["verified"] and fixed_summary["N"] == 25 and fixed_summary["B"] == 14
    assert fixed_summary["parent_catalog_sha256"] == groups_digest
    assert fixed_summary["source_sha256"] == sha(ROOT / "pay_prior_fixed_branches.py")
    fixed_ids = {gid for gid, p in {**post_paid, **force_paid}.items()
                 if "completion-family" in p["kind"] and groups[gid]["centers"] < 25}
    assert set(fixed_summary["selected_parent_groups"]) == fixed_ids
    refinements = {}
    for path in args.refinement_exact:
        accepted = read(path)
        assert accepted["verified"] and accepted["schema"] == "same-topology-hole-force-refinement-exact-v1"
        assert (accepted["N"], accepted["B"]) == (25, 14)
        assert accepted["source_sha256"] == sha(ROOT / "replay_refined_hole_leaves.py")
        assert accepted["whole_tree_fresh_exact_replayed"] and accepted["only_original_FULL_PENDING_leaves_changed"]
        unchanged(accepted["files_relative_to_workspace"])
        key = tuple(accepted["collar_faces"])
        assert key not in refinements
        targets = [WORK / rel for rel in accepted["files_relative_to_workspace"]
                   if (WORK / rel).name == "REFINED.json" or "force31-refinement-" in (WORK / rel).name
                   and "exact" not in (WORK / rel).name]
        assert len(targets) == 1
        refinements[key] = (path.resolve(), targets[0], accepted)
    simple_controls = read(ROOT / "n25-paid-hole-controls-20261005-v1/VERIFIED.json")
    assert simple_controls["verified"] and simple_controls["kernel_sha256"] == sha(ROOT / "proof_paid_hole_kernel.py")
    assert simple_controls["source_induction_sha256"] == sha(ROOT / "PROOF-PAID-HOLE-SOURCE.md")
    assert simple_controls["source_sha256"] == sha(ROOT / "test_paid_hole.py")
    unchanged(simple_controls["files_relative_to_workspace"])
    general_controls = read(ROOT / "n25-linked-general-collar-controls-20261005-v1/VERIFIED.json")
    assert general_controls["verified"] and general_controls["kernel_sha256"] == sha(ROOT / "linked_general_collar_kernel.py")
    assert general_controls["source_induction_sha256"] == sha(ROOT / "GENERAL-COLLAR-FILLING-SOURCE.md")
    assert general_controls["source_sha256"] == sha(ROOT / "test_linked_general_collar.py")
    unchanged(general_controls["files_relative_to_workspace"])
    pinched_report = read(pinched / "VERIFIED.json")
    assert pinched_report["verified"] and pinched_report["schema"] == "complete-pinched-residual-subset-payment-v1"
    assert pinched_report["source_sha256"] == sha(ROOT / "pay_pinched_residual.py")
    assert pinched_report["parent_report_sha256"] == sha(force / "VERIFIED.json")
    assert pinched_report["all_parent_pinched_rows_selected_and_processed_once"]
    assert sha(pinched / "PAYMENTS.jsonl") == pinched_report["payments_sha256"]
    pinched_paid = ledger(pinched / "PAYMENTS.jsonl", groups)
    unchanged(pinched_report["files_relative_to_workspace"])
    assert set(pinched_paid) <= set(last_remaining)
    output.mkdir()
    counts, pending = Counter(), {}
    byid = {o["id"]: o for o in strict_library["obstacles"]}
    raw_stage = ROOT / "n25-B14-old-complete-force-stage-20261005-v1"
    def pay_fixed_branch(gid, centers, faces):
        directory = fixed_branches / f"parent-{gid:07}"
        accepted, status = read(directory / "EXACT.json"), read(directory / "STATUS.json")
        assert accepted["verified"] and accepted["source_sha256"] == sha(ROOT / "replay_paid_hole.py")
        assert (accepted["N"], accepted["B"], accepted["collar_centers"], accepted["collar_faces"]) == (
            25, 14, centers, faces)
        assert status["exact_sha256"] == sha(directory / "EXACT.json")
        assert status["proposal_sha256"] == sha(directory / "PROPOSAL.json")
        checked = simple_replay(directory / "PROPOSAL.json", constants)
        same_branch_result(checked, accepted)
        assert checked["all_full_simple_disk_completions_strictly_paid"]
        for path in (directory / "EXACT.json", directory / "PROPOSAL.json", directory / "STATUS.json"):
            bind(files, path)
    ledgers = output / "ALL-PARENT-PAYMENTS.jsonl"
    with ledgers.open("x", encoding="ascii") as target:
        for gid, group in enumerate(groups):
            centers, faces = group["centers"], group["faces"]
            if centers == 25:
                # Apply the stronger actual-cover necessity to the whole
                # parent, including types paid earlier by a different route.
                kind = "actual-cover-origin-unexposed-center-obstruction"
                assert exposed_mask(centers, 14, faces) == (1 << 25)-1 and gap > 0
            elif gid in post_paid:
                payment = post_paid[gid]
                kind = payment["kind"]
                if kind == "strict-sparse-source-injection":
                    obstacle = byid[payment["obstacle"]]
                    validate(25, 14, obstacle["faces"], payment["map"], faces)
                elif kind == "strict-eight-rod-integer-angle-cycle":
                    assert verify_cycle(14, centers, faces, payment["cycle"], constants) == payment["exact_cycle_check"]
                else:
                    assert kind == "strict-full-simple-disk-completion-family"
                    pay_fixed_branch(gid, centers, faces)
                    kind = "fresh-branch-payment-for-prior-fixed-family"
            elif gid in origin_paid:
                kind = "actual-cover-origin-unexposed-center-obstruction"
                payment = origin_paid[gid]
                assert payment["kind"] == kind and F(payment["radius_upper"]) == U
                assert F(payment["strict_gap_1_minus_4U"]) == gap > 0
                assert centers == 25 and exposed_mask(centers, 14, faces) == (1 << 25)-1
            elif gid in force_paid:
                payment = force_paid[gid]
                kind = payment["kind"]
                if kind == "fresh-standard-library-exact-weak-force":
                    treepath = raw_stage / f"group-{gid:07}.json.gz"
                    assert sha(treepath) == payment["tree_sha256"]
                    with gzip.open(treepath, "rt", encoding="utf8") as stream:
                        tree = json.load(stream, object_pairs_hook=no_duplicate_keys)
                    assert (tree["N"], tree["B"], tree["partial_centers"], tree["faces"]) == (25, 14, centers, faces)
                    assert tree["groups_sha256"] == groups_digest and tree["constants_sha256"] == constants_digest
                    assert F(tree["radius_upper"]) == U
                    checked = exact.verify(14, centers, faces, tree["nodes"], constants)
                    assert checked["verified"] and F(checked["minimum_force_margin"]) > 0
                    assert sha(treepath) == payment["tree_sha256"]
                    bind(files, treepath)
                else:
                    assert kind == "strict-complete-simple-disk-completion-family"
                    pay_fixed_branch(gid, centers, faces)
                    kind = "fresh-branch-payment-for-prior-fixed-family"
            else:
                assert gid in last_remaining
                payment = None
                if tuple(faces) in refinements:
                    exactpath, proposalpath, accepted = refinements[tuple(faces)]
                    assert accepted["collar_centers"] == centers
                    result = simple_replay(proposalpath, constants)
                    same_branch_result(result, accepted)
                    if result["all_full_simple_disk_completions_strictly_paid"]:
                        kind = "refined-exact-complete-simple-hole-family"
                        payment = {"parent_group": gid, "exact_report_sha256": sha(exactpath)}
                        bind(files, exactpath);bind(files, proposalpath)
                elif gid in pinched_paid:
                    directory = pinched / f"parent-{gid:07}"
                    exactpath, proposalpath = directory / "EXACT.json", directory / "PROPOSAL.json"
                    accepted = read(exactpath)
                    assert accepted["source_sha256"] == sha(ROOT / "replay_linked_general_collar.py")
                    assert (accepted["N"], accepted["B"]) == (25, 14)
                    assert (accepted["collar_centers"], accepted["collar_faces"]) == (centers, faces)
                    assert pinched_paid[gid]["exact_sha256"] == sha(exactpath)
                    result = general_replay(proposalpath, constants)
                    same_branch_result(result, accepted)
                    assert result["all_full_simple_disk_completions_strictly_paid"]
                    kind = "exact-complete-pinched-collar-filling-family"
                    payment = {"parent_group": gid, "exact_report_sha256": sha(exactpath)}
                    bind(files, exactpath);bind(files, proposalpath)
                else:
                    directory = simple / f"parent-{gid:07}"
                    statuspath = directory / "STATUS.json"
                    if statuspath.exists():
                        status = read(statuspath)
                        assert status["parent_group"] == gid
                        if status["status"] == "strictly-paid-complete-simple-hole-family":
                            exactpath, proposalpath = directory / "EXACT.json", directory / "PROPOSAL.json"
                            accepted = read(exactpath)
                            assert accepted["source_sha256"] == sha(ROOT / "replay_paid_hole.py")
                            assert (accepted["N"], accepted["B"]) == (25, 14)
                            assert (accepted["collar_centers"], accepted["collar_faces"]) == (centers, faces)
                            assert status["exact_sha256"] == sha(exactpath) and status["proposal_sha256"] == sha(proposalpath)
                            result = simple_replay(proposalpath, constants)
                            same_branch_result(result, accepted)
                            assert result["all_full_simple_disk_completions_strictly_paid"]
                            kind = "exact-complete-simple-hole-family"
                            payment = {"parent_group": gid, "exact_report_sha256": sha(exactpath)}
                            bind(files, statuspath);bind(files, exactpath);bind(files, proposalpath)
                if payment is None:
                    kind = "unpaid"
                    pending[gid] = group
            counts[kind] += 1
            target.write(json.dumps({"parent_group": gid, "kind": kind,
                                     "not_a_global_N25_completion_claim": True},
                                    separators=(",", ":"))+"\n")
            if gid % 5000 == 0:
                target.flush()
                print("Independent all-parent B14 chain audit:", gid+1, "/", total, dict(counts), flush=True)
    assert sum(counts.values()) == total
    residualpath = output / "RESIDUAL.jsonl"
    with residualpath.open("x", encoding="ascii") as stream:
        stream.write(json.dumps({"N": 25, "B": 14, "parent_catalog_sha256": sha(groupspath),
                                 "schema": "independent-all-parent-B14-chain-residual-v1"})+"\n")
        for gid in sorted(pending):
            stream.write(json.dumps(pending[gid], separators=(",", ":"))+"\n")
    for path in (
        Path(__file__), constants_path, base / "SUMMARY.json", base / "NATIVE-TERMINAL.json",
        base / "INPUT-BINDINGS.json", base / "NATIVE-STDERR.log", catalogpath, groupspath, bindingpath,
        postfilter / "VERIFIED.json", postfilter / "PAYMENTS.jsonl", postfilter / "RESIDUAL.jsonl",
        origin / "VERIFIED.json", origin / "ORIGIN-PAYMENTS.jsonl", origin / "RESIDUAL.jsonl",
        force / "VERIFIED.json", force / "PAYMENTS.jsonl", force / "RESIDUAL.jsonl",
        pinched / "VERIFIED.json", pinched / "PAYMENTS.jsonl",
        fixed_branches / "SUMMARY.json",
        ROOT / "n25-paid-hole-controls-20261005-v1/VERIFIED.json",
        ROOT / "n25-linked-general-collar-controls-20261005-v1/VERIFIED.json",
        ROOT / "N25-COLLAR-COVER-INTERFACE.md", ROOT / "UNEXPOSED-ORIGIN-CENTER-SOURCE.md",
        ROOT / "PROOF-PAID-HOLE-SOURCE.md", ROOT / "GENERAL-COLLAR-FILLING-SOURCE.md",
        ROOT / "proof_paid_hole_kernel.py", ROOT / "linked_general_collar_kernel.py",
        HIGH / "exact_graph.py", ROOT / "eight_rod_angles.py",
    ):
        bind(files, path)
    unchanged(files)
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "independent-all-parent-N25-B14-lower-payment-chain-v1",
        "N": 25, "B": 14, "complete_necessary_parent_weak_graphs": total,
        "each_parent_id_has_exactly_one_final_status": True,
        "all_stage_payment_residual_partitions_compared_by_parent_identity": True,
        "all_selected_branch_force_trees_and_topology_children_fresh_replayed": True,
        "strict_library_trees_fresh_reaccepted": True, "payment_counts": dict(counts),
        "pending_weak_graphs": len(pending), "complete_B14_actual_cover_lower_family_paid": not pending,
        "no_arbitrary_cover_strictly_below_exact_rstar_with_reduced_B14_proved": not pending,
        "actual_cover_origin_condition_not_a_geometric_weak_graph_exclusion": True,
        "fixed_completion_family_payments_not_a_geometric_weak_graph_exclusion": True,
        "radius_upper": str(U), "exact_candidate_radius": "1/(sqrt(6)+sqrt(3))",
        "all_parent_ledger_sha256": sha(ledgers), "residual_sha256": sha(residualpath),
        "files_relative_to_workspace": files, "source_sha256": sha(Path(__file__)),
        "B15_B16_B17_not_paid_here": True, "global_optimality_proved": False,
    })
    print("Independent full B14 chain accepted:", dict(counts), "; pending:", len(pending), flush=True)


if __name__ == "__main__":
    main()
