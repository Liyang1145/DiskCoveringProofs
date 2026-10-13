"""Complete small-union batch proof/replay controls, plus independent corruptions."""
from pathlib import Path
import argparse
import gzip
import json
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from n25_outer_search import read, publish
from batch_streamed_collar import partition
from audit_collar_batch_payments import audit, verify_tree
from batch_streamed_collar import identity
from group_catalog import canonical_full

assert __debug__


def write_fixture(path, value):
    """Only deliberately corrupt freshly copied disposable control fixtures."""
    path.write_text(json.dumps(value, indent=2)+"\n", encoding="utf8")


def invoke(script, args, directory, label):
    scriptpath = ROOT / script if script == "probe_collar_batches.py" else HIGH / script
    result = subprocess.run([sys.executable, str(scriptpath), *map(str, args)],
                            capture_output=True, creationflags=subprocess.CREATE_NO_WINDOW)
    publish(directory / (label+"-TERMINAL.json"), {
        "actual_exit_code": result.returncode, "source_sha256": sha(scriptpath),
        "stdout": result.stdout.decode("utf8", errors="replace"),
        "stderr": result.stderr.decode("utf8", errors="replace"),
    })
    assert result.returncode == 0, (script, result.stdout, result.stderr)


def sampled_n25_proof_controls(output):
    """Finite positive/attaining controls, never mislabelled as a complete union."""
    source = read(ROOT / "n25-B14-ring21-simple-hole-completions-20261005-v1/GROUPS.json")
    constants_path = HIGH.parent / "evidence/core-reduction/constants/n25.json"
    constants = read(constants_path)
    strict = output / "FINITE-N25-STRICT-CONTROL"
    strict.mkdir()
    groups = [{**r, "id": j, "members": 1} for j, r in enumerate(source["groups"][:3])]
    geometry = read(HIGH.parent / "evidence/n25-algebraic-upper-round2/geometry.json")
    known_faces = list(canonical_full(25, 16, sorted(sum(1 << v for v in face) for face in geometry["faces"])))
    results = []
    for directory, B, rows in (
        (strict, 14, groups),
        (output / "FINITE-N25-ATTAINING-CONTROL", 16,
         [{"id": 0, "centers": 25, "faces": known_faces, "members": 1}]),
    ):
        if not directory.exists():
            directory.mkdir()
        bindings = directory / "bindings.jsonl"
        bindings.write_text("".join(json.dumps({"index": j, "group": j,
                                                "map": identity(r["centers"], B)})+"\n"
                                    for j, r in enumerate(rows)), encoding="ascii")
        groupspath = directory / "GROUPS.json"
        publish(groupspath, {
            "N": 25, "B": B, "threshold": 0, "groups": rows, "group_count": len(rows),
            "selected_types": len(rows), "catalog_types": len(rows),
            "bindings_file": bindings.name, "bindings_sha256": sha(bindings),
            "verified_embeddings_during_generation": True, "full_selected_catalog_scanned": False,
            "finite_arithmetic_controls_only_not_complete_catalog": True,
        })
        invoke("probe_collar_batches.py", ["--groups", groupspath, "--output", directory / "PROPOSALS",
                                           "--limit", "1", "--route-weak-realizable"], directory, "PROPOSE")
        receiptpath = directory / "PROPOSALS/SUMMARY.json"
        invoke("replay_group_stage.py", ["--groups", groupspath, "--receipt", receiptpath,
                                         "--output", directory / "EXACT-REPLAY.json"], directory, "REPLAY")
        receipt = read(receiptpath)
        if B == 14:
            assert receipt["excluded_groups"] == 3 and receipt["pending_groups"] == 0
            for group, outcome in zip(rows, receipt["outcomes"], strict=True):
                verify_tree(25, B, group, outcome, receiptpath, sha(groupspath),
                            constants, sha(constants_path))
        else:
            assert receipt["known_attaining_group_control"] == 0
            assert receipt["excluded_groups"] == 0 and receipt["pending_groups"] == 1
        results.append({"B": B, "finite_groups": len(rows), "strict": receipt["excluded_groups"],
                        "pending": receipt["pending_groups"], "receipt_sha256": sha(receiptpath),
                        "exact_replay_sha256": sha(directory / "EXACT-REPLAY.json")})
    bad = output / "BAD-TREE-RADIUS-CONTROL"
    shutil.copytree(strict, bad)
    groupspath, receiptpath = bad / "GROUPS.json", bad / "PROPOSALS/SUMMARY.json"
    group, outcome = read(groupspath)["groups"][0], read(receiptpath)["outcomes"][0]
    treepath = receiptpath.parent / "group-0000000.json.gz"
    with gzip.open(treepath, "rt", encoding="utf8") as stream:
        tree = json.load(stream)
    tree["radius_upper"] = "1/4"
    with gzip.open(treepath, "wt", encoding="utf8") as stream:
        json.dump(tree, stream)
    outcome["tree_sha256"] = sha(treepath)
    try:
        verify_tree(25, 14, group, outcome, receiptpath, sha(groupspath), constants, sha(constants_path))
    except AssertionError as error:
        assert str(error) == "tree radius threshold mismatch"
    else:
        raise AssertionError("accepted a modified arithmetic threshold")
    return results


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    output.mkdir()
    derivation = read(ROOT / "collar-batch-proposer-derivation.json")
    assert derivation["original_source_sha256"] == sha(HIGH / "probe_groups.py")
    assert derivation["derived_source_sha256"] == sha(ROOT / "probe_collar_batches.py")
    assert derivation["source_sha256"] == sha(ROOT / "derive_collar_batch_proposer.py")
    text = (HIGH / "probe_groups.py").read_text(encoding="utf8")
    for (before, after), count in zip(derivation["changes"], derivation["occurrence_counts"], strict=True):
        assert text.count(before) == count
        text = text.replace(before, after)
    assert text == (ROOT / "probe_collar_batches.py").read_text(encoding="utf8")
    case = ROOT / "n25-streamed-collar-controls-20261005-v1/N21-dfs-slab7-sparse0"
    manifestpath, terminalpath, unionpath = case / "MANIFEST.json", case / "NATIVE-TERMINAL.json", case / "UNION/VERIFIED.json"
    main_partition = output / "MAIN"
    result = partition(manifestpath, terminalpath, unionpath, main_partition, 5)
    assert result["weak_graph_count"] == 18 and result["batch_count"] == 4
    descriptors = [json.loads(line) for line in (main_partition / "BATCHES.jsonl").read_text().splitlines()]
    for descriptor in descriptors:
        groupspath = main_partition / descriptor["groups_file"]
        directory = groupspath.parent
        invoke("probe_collar_batches.py", ["--groups", groupspath, "--output", directory / "PROPOSALS",
                                  "--limit", "1", "--route-weak-realizable"], directory, "PROPOSE")
        invoke("replay_group_stage.py", ["--groups", groupspath,
                                        "--receipt", directory / "PROPOSALS/SUMMARY.json",
                                        "--output", directory / "EXACT-REPLAY.json"], directory, "REPLAY")
        print("Bounded proof and exact replay accepted: batch", descriptor["batch"], flush=True)
    accepted = audit(manifestpath, terminalpath, unionpath, main_partition / "VERIFIED.json", output / "ACCEPTED")
    assert accepted["parent_weak_graphs"] == 18
    assert accepted["strictly_excluded"]+accepted["pending_weak_graphs"] == 18
    print("Complete batch audit PASS:", accepted["strictly_excluded"], "strict;",
          accepted["pending_weak_graphs"], "pending", flush=True)
    finite_controls = sampled_n25_proof_controls(output)
    rejected = ["tree-radius-threshold"]
    badterminal = output / "NONZERO-TERMINAL.json"
    terminal = read(terminalpath)
    terminal["actual_exit_code"] = 1
    publish(badterminal, terminal)
    try:
        partition(manifestpath, badterminal, unionpath, output / "BAD-EXIT-PARTITION", 5)
    except AssertionError:
        rejected.append("nonzero-native-exit")
    else:
        raise AssertionError("accepted a nonzero parent")
    for label in ("missing-first-batch", "duplicate-batch"):
        clone = output / ("BAD-"+label)
        shutil.copytree(main_partition, clone)
        changed = descriptors[1:] if label == "missing-first-batch" else descriptors[:1]+descriptors
        descriptorpath = clone / "BATCHES.jsonl"
        descriptorpath.write_text("".join(json.dumps(r)+"\n" for r in changed), encoding="ascii")
        report = read(clone / "VERIFIED.json")
        report["descriptor_sha256"] = sha(descriptorpath)
        write_fixture(clone / "VERIFIED.json", report)
        try:
            audit(manifestpath, terminalpath, unionpath, clone / "VERIFIED.json", output / (label+"-AUDIT"))
        except AssertionError as error:
            assert str(error) == "batch index/range gap or duplication", str(error)
            rejected.append(label)
        else:
            raise AssertionError(("accepted invalid partition", label))
    clone = output / "BAD-identity"
    shutil.copytree(main_partition, clone)
    rows = [dict(r) for r in descriptors]
    group = clone / rows[0]["groups_file"]
    bindingpath = group.parent / "bindings.jsonl"
    bindings = [json.loads(line) for line in bindingpath.read_text().splitlines()]
    bindings[0]["map"]["anchors"][0] = 1
    bindingpath.write_text("".join(json.dumps(r)+"\n" for r in bindings), encoding="ascii")
    data = read(group)
    data["bindings_sha256"] = sha(bindingpath)
    write_fixture(group, data)
    rows[0]["groups_sha256"], rows[0]["bindings_sha256"] = sha(group), sha(bindingpath)
    descriptorpath = clone / "BATCHES.jsonl"
    descriptorpath.write_text("".join(json.dumps(r)+"\n" for r in rows), encoding="ascii")
    report = read(clone / "VERIFIED.json")
    report["descriptor_sha256"] = sha(descriptorpath)
    write_fixture(clone / "VERIFIED.json", report)
    receiptpath, replaypath = group.parent / "PROPOSALS/SUMMARY.json", group.parent / "EXACT-REPLAY.json"
    receipt, replay = map(read, (receiptpath, replaypath))
    receipt["groups_sha256"] = replay["groups_sha256"] = sha(group)
    write_fixture(receiptpath, receipt)
    replay["bindings_sha256"], replay["receipt_sha256"] = sha(bindingpath), sha(receiptpath)
    write_fixture(replaypath, replay)
    try:
        audit(manifestpath, terminalpath, unionpath, clone / "VERIFIED.json", output / "BAD-identity-AUDIT")
    except AssertionError as error:
        assert str(error) == "batch identity binding mismatch", str(error)
        rejected.append("self-consistent-wrong-anchor-binding")
    else:
        raise AssertionError("accepted a wrong identity map")
    zero = ROOT / "n25-streamed-collar-controls-20261005-v1/N20-dfs-slab1-sparse0"
    empty = partition(zero / "MANIFEST.json", zero / "NATIVE-TERMINAL.json", zero / "UNION/VERIFIED.json",
                      output / "EMPTY", 5)
    assert empty["weak_graph_count"] == empty["batch_count"] == 0
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "complete-collar-bounded-payment-controls-v1",
        "all_18_parent_graphs_partitioned_once_and_audited": True,
        "four_real_proposal_and_stdlib_replay_batches_completed": True,
        "strictly_excluded": accepted["strictly_excluded"], "pending_weak_graphs": accepted["pending_weak_graphs"],
        "pending_not_misreported_as_exclusions": True, "empty_complete_union_partition_checked": True,
        "negative_controls_rejected": rejected,
        "partition_sha256": sha(main_partition / "VERIFIED.json"),
        "complete_payment_audit_sha256": sha(output / "ACCEPTED/VERIFIED.json"),
        "source_sha256": sha(Path(__file__)),
        "partition_source_sha256": sha(ROOT / "batch_streamed_collar.py"),
        "audit_source_sha256": sha(ROOT / "audit_collar_batch_payments.py"),
        "frozen_proposer_sha256": sha(HIGH / "probe_groups.py"),
        "derived_proposer_sha256": sha(ROOT / "probe_collar_batches.py"),
        "proposer_derivation_sha256": sha(ROOT / "collar-batch-proposer-derivation.json"),
        "frozen_replayer_sha256": sha(HIGH / "replay_group_stage.py"),
        "no_production_catalog_paid_by_this_control": True, "global_optimality_proved": False,
        "separate_finite_n25_exact_controls": finite_controls,
        "all_three_finite_n25_strict_controls_fresh_replayed": True,
        "known_n25_attaining_control_not_strictly_excluded": True,
    })


if __name__ == "__main__":
    main()
