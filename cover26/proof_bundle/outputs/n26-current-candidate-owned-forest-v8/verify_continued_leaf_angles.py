"""Independent semantic acceptance of closed continuation after leaf pinning."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
from n26_force import load_trig
import n26_current_leaf_angle_source as current


leaf = current.leaf
sha = leaf.sha


def proposal_gate(source, source_folder, proposal):
    if (proposal["source_acceptance_sha256"] != sha(source_folder / "VERIFIED.json")
            or proposal["source_certificate_sha256"] != sha(source_folder / "CERTIFICATE.json")
            or proposal["spec"] != source["spec"] or proposal["radius_scope"] != "same-root-Rstar"):
        raise ValueError("continued leaf proposal changed its accepted source or radius")
    leaf.lineage_gate(source["nodes"], proposal["nodes"])


def replay_and_close(values, proposal, arcs):
    nodes = deepcopy(proposal["nodes"])
    _, pending, _ = leaf.replay(
        values["source"]["spec"], values["radius"], values["cells"], values["matrix"],
        values["cap"], values["reference"], values["data"], nodes, arcs)
    empty, local = [], []
    for row in pending:
        if row["sharp_radius_domain_empty"]:
            nodes[row["index"]] = {"kind": "SHARP_EMPTY"}
            empty.append(row["index"])
        elif row["sharp_radius_domain_inside_local"]:
            nodes[row["index"]] = {"kind": "SHARP_LOCAL"}
            local.append(row["index"])
    leaf.lineage_gate(values["source"]["nodes"], nodes)
    result, pending, ledger = leaf.replay(
        values["source"]["spec"], values["radius"], values["cells"], values["matrix"],
        values["cap"], values["reference"], values["data"], nodes, arcs, progress=True)
    return nodes, result, pending, ledger, empty, local


def main():
    parser = argparse.ArgumentParser()
    for name in ("source", "correlated", "sharp", "historical", "pinning-basis", "stress",
                 "local", "transport", "pinning", "caps", "proposal", "output"):
        parser.add_argument("--" + name, type=Path, required=True)
    args = parser.parse_args()
    for key in vars(args):
        setattr(args, key, getattr(args, key).resolve())
    if args.output.exists():
        raise FileExistsError(args.output)
    values = current.input_gate(args.source, args.correlated, args.sharp, args.historical, args.pinning_basis,
                                args.stress, args.local, args.transport, args.pinning, args.caps)
    hashes = {linux(path): sha(path) for path in values["inventory"]}
    proposal = json.loads(args.proposal.read_text())
    proposal_gate(values["source"], args.source, proposal)
    arcs = load_trig(args.source)[0]
    nodes, result, pending, ledger, empty, local = replay_and_close(values, proposal, arcs)
    negatives = []

    def reject(label, fn):
        try:
            fn()
        except (ValueError, KeyError, TypeError, IndexError):
            negatives.append(label)
        else:
            raise AssertionError("invalid continued leaf proof accepted: " + label)

    bad = deepcopy(nodes)
    next(node for node in bad if node["kind"] == leaf.HULL_LOCAL)["kind"] = "OPEN"
    reject("old-hull-local-erased", lambda: leaf.lineage_gate(values["source"]["nodes"], bad))
    bad = deepcopy(nodes)
    next(node for node in bad if node["kind"] == "SHARP_CORRELATED_FORCE")["kind"] = "OPEN"
    reject("old-correlated-force-erased", lambda: leaf.lineage_gate(values["source"]["nodes"], bad))
    bad = deepcopy(nodes)
    split = next(node for node in bad[len(values["source"]["nodes"]):] if node["kind"] == "SPLIT")
    split["children"][1] = split["children"][0]
    reject("new-closed-split-lost-half", lambda: leaf.replay(
        values["source"]["spec"], values["radius"], values["cells"], values["matrix"],
        values["cap"], values["reference"], values["data"], bad, arcs))
    reject("unreachable-new-open", lambda: leaf.replay(
        values["source"]["spec"], values["radius"], values["cells"], values["matrix"],
        values["cap"], values["reference"], values["data"], nodes + [{"kind": "OPEN"}], arcs))
    bad_proposal = deepcopy(proposal)
    bad_proposal["radius_scope"] = "at-most-U"
    reject("silently-changed-radius-scope", lambda: proposal_gate(values["source"], args.source, bad_proposal))
    tiny = [tuple(map(F, row)) for row in values["cap"]["known_candidate_tiny_angle_cells"]]
    retained = any(row["kind"] in ("LOCAL", "SHARP_LOCAL") and all(
        F(lo) <= a <= b <= F(hi) for lo, hi, (a, b) in zip(
            row.get("sharp_lower", row["lower"]), row.get("sharp_upper", row["upper"]), tiny))
        for row in ledger if row["kind"] in ("LOCAL", "SHARP_LOCAL"))
    if not retained:
        raise ValueError("continued leaf tree lost known root tiny-box positive control")
    old_counts = values["accepted"]["counts"]
    force_kinds = ("FORCE", "SHARP_FORCE", "SHARP_CORRELATED_FORCE")
    new_force = sum(result["counts"][kind] - old_counts[kind] for kind in force_kinds)
    new_hull = result["counts"][leaf.HULL_LOCAL] - old_counts[leaf.HULL_LOCAL]
    sources = {"starting_partition": sha(args.source / "VERIFIED.json"),
               "pinning_reference": sha(args.pinning / "VERIFIED.json"), "sharp_caps": sha(args.caps / "VERIFIED.json"),
               "stress": sha(args.stress / "VERIFIED.json"), "local": sha(args.local / "VERIFIED.json"),
               "transport": sha(args.transport / "VERIFIED.json")}
    certificate = {"schema": "N26-continued-leaf-pinned-closed-angular-tree-v1",
                   "radius_scope": "same-root-Rstar", "spec": values["source"]["spec"],
                   "source_acceptance_sha256": sources, "nodes": nodes}
    args.output.mkdir(parents=True)
    files = []
    for name, obj in (("CERTIFICATE.json", certificate), ("PENDING-ANGLES.json", pending), ("LOWER-LEDGER.json", ledger)):
        (args.output / name).write_text(json.dumps(obj, separators=(",", ":")) + "\n", encoding="utf-8")
        files.append(name)
    for original, name in ((args.proposal, "PROPOSAL.json"), (args.source / "CERTIFICATE.json", "SOURCE-CERTIFICATE.json"),
                           (args.source / "VERIFIED.json", "SOURCE-ACCEPTANCE.json")):
        (args.output / name).write_bytes(original.read_bytes())
        files.append(name)
    for name in values["accepted"]["files"]:
        if name.endswith(".py"):
            (args.output / name).write_bytes((args.source / name).read_bytes())
            files.append(name)
    for name in ("n26_current_leaf_angle_source.py", "verify_continued_leaf_angles.py"):
        (args.output / name).write_bytes(Path(__file__).with_name(name).read_bytes())
        files.append(name)
    proof = Path(__file__).with_name("n26-continued-leaf-angles-proof.md")
    if not proof.exists():
        proof = Path(__file__).with_name("PROOF.md")
    (args.output / "PROOF.md").write_bytes(proof.read_bytes())
    files.append("PROOF.md")
    if any(sha(leaf.local_path(text)) != digest for text, digest in hashes.items()):
        raise ValueError("continued leaf dependency bytes changed during acceptance")
    report = {"schema": "N26-accepted-continued-leaf-pinned-angular-tree-v1",
              "verified": True, **result, "source_acceptance_sha256": sources,
              "prior_all_proved_nodes_and_closed_splits_preserved": True,
              "known_exact_candidate_tiny_box_retained_in_proved_LOCAL_leaf": retained,
              "new_strict_force_leaves": new_force, "new_paid_hull_local_leaves": new_hull,
              "new_complete_closed_splits": result["counts"]["SPLIT"] - old_counts["SPLIT"],
              "automatically_paid_sharp_empty_indices": empty, "automatically_paid_sharp_local_indices": local,
              "negative_controls_rejected": negatives, "discovery_numbers_not_used_as_proof": True,
              "current_global_combinatorial_frontier_nodes_removed": 0,
              "formal_machine_geometry_proof": False, "full_catalog_complete": False,
              "global_lower_bound_proved": False, "global_optimality_proved": False,
              "files": {name: sha(args.output / name) for name in dict.fromkeys(files)}, "source_files": hashes}
    (args.output / "VERIFIED.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items() if key not in ("files", "source_files")}, indent=2), flush=True)


if __name__ == "__main__":
    main()
