"""Freeze a correctly scoped conditional extension of the unchanged base kernel."""

import argparse
import json
from pathlib import Path
import subprocess
import sys

from audit_prefix_partition import linux
from verify_conditional_force_stage import SCOPE, bound, local_path, read, sha, scope_gate


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--proposal", type=Path, required=True)
    parser.add_argument("--source-replay", type=Path, required=True)
    parser.add_argument("--radius-basis", type=Path, required=True)
    parser.add_argument("--radius-basis-replay", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    proposal = read(args.proposal)
    accepted_path = local_path(proposal["source_acceptance_original_path"])
    source_path = local_path(proposal["source_frontier_original_path"])
    accepted = bound(accepted_path.parent)[0]
    basis = bound(args.radius_basis)[0]
    if (accepted["radius_scope"] != SCOPE
            or read(args.source_replay) != accepted or read(args.radius_basis_replay) != basis
            or proposal["source_acceptance_sha256"] != sha(accepted_path)
            or proposal["source_frontier_sha256"] != sha(source_path)):
        raise ValueError("conditional discovery changed its accepted source or actual replay")
    command = [sys.executable, str(Path(__file__).with_name("build_force_stage_bundle.py")),
               "--proposal", str(args.proposal), "--output", str(args.output)]
    run = subprocess.run(command, check=False)
    if run.returncode:
        raise ValueError("conditional bundle base construction failed; partial output preserved")
    manifest, trace = read(args.output / "MANIFEST.json"), read(args.output / "TRACE.json")
    original_proof = args.output / "PROOF.md"
    (args.output / "BASE-U-SUFFICIENT-PROOF.md").write_bytes(original_proof.read_bytes())
    copies = [
        (Path(__file__).with_name("verify_conditional_force_stage.py"), "verify_conditional_force_stage.py"),
        (Path(__file__), "build_conditional_force_stage.py"),
        (args.radius_basis / "VERIFIED.json", "RADIUS-BASIS-ACCEPTANCE.json"),
        (args.radius_basis / "CATALOG-SOURCE/CANDIDATE-PATH.json", "CANDIDATE-PATH.json"),
        (args.proposal, "PROPOSAL.json")]
    proof = Path(__file__).with_name("n26-conditional-force-stage-proof.md")
    if not proof.exists():
        proof = Path(__file__).with_name("PROOF.md")
    copies.append((proof, "PROOF.md"))
    for original, name in copies:
        (args.output / name).write_bytes(original.read_bytes())
    manifest.update({
        "schema": "N26-successive-radius-conditional-stage-input-bindings-v1", "radius_scope": SCOPE,
        "radius_upper": basis["radius_upper"], "screen_radius_threshold": proposal["radius_threshold"],
        "inherited_source_is_unconditional_at_U": False,
        "source_published_replay": linux(args.source_replay),
        "source_published_replay_sha256": sha(args.source_replay),
        "radius_basis": linux(args.radius_basis),
        "radius_basis_published_replay": linux(args.radius_basis_replay),
        "radius_basis_acceptance_sha256": sha(args.radius_basis / "VERIFIED.json"),
        "conditional_builder_sha256": sha(__file__)})
    manifest["copied_files"].update({name: sha(args.output / name) for _, name in copies})
    manifest["copied_files"]["BASE-U-SUFFICIENT-PROOF.md"] = sha(args.output / "BASE-U-SUFFICIENT-PROOF.md")
    trace.update({"schema": "N26-successive-radius-conditional-stage-trace-v1", "radius_scope": SCOPE})
    (args.output / "TRACE.json").write_text(json.dumps(trace, separators=(",", ":")) + "\n", encoding="utf-8")
    manifest["trace_sha256"] = sha(args.output / "TRACE.json")
    scope_gate(manifest, accepted, read(source_path), basis)
    (args.output / "MANIFEST.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"built": True, "verified": False, "radius_scope": SCOPE,
                      "screen_radius_threshold": proposal["radius_threshold"],
                      "events": len(trace["events"]), "native_and_exact_acceptance_pending": True}), flush=True)


if __name__ == "__main__":
    main()
