"""Fresh sparse-event bundle; preserve historical checkers and failed bundles."""

import argparse
import json
from pathlib import Path
import subprocess
import sys

import n26_sparse_stage_controls as control


def main():
    parser = argparse.ArgumentParser()
    for name in ("proposal", "source-replay", "radius-basis", "radius-basis-replay",
                 "control-regression", "output"):
        parser.add_argument("--" + name, type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    command = [sys.executable, str(Path(__file__).with_name("build_conditional_force_stage.py"))]
    for name in ("proposal", "source-replay", "radius-basis", "radius-basis-replay", "output"):
        command.extend(("--" + name, str(getattr(args, name.replace("-", "_")))))
    run = subprocess.run(command, check=False)
    if run.returncode:
        raise ValueError("sparse base build failed; partial output preserved")
    manifest = control.exact.read(args.output / "MANIFEST.json")
    copies = [
        (Path(__file__), Path(__file__).name),
        (Path(__file__).with_name("verify_conditional_force_stage_sparse.py"),
         "verify_conditional_force_stage_sparse.py"),
        (Path(control.__file__), "n26_sparse_stage_controls.py"),
        (Path(__file__).with_name("test_sparse_stage_controls.py"), "test_sparse_stage_controls.py"),
        (args.control_regression, "CONTROL-SELECTOR-REGRESSION.json"),
        (Path(__file__).with_name("n26-sparse-stage-control-proof.md"), "SPARSE-CONTROL-PROOF.md"),
    ]
    for path, name in copies:
        (args.output / name).write_bytes(path.read_bytes())
    fixture, _ = control.select_control(args.output)
    target = args.output / "ANGULAR-REGRESSION-CONTROL.json"
    target.write_text(json.dumps(fixture, indent=2) + "\n", encoding="utf-8")
    manifest["copied_files"].update({
        name: control.exact.sha(args.output / name) for _, name in copies})
    manifest["copied_files"][target.name] = control.exact.sha(target)
    manifest["sparse_event_control_policy"] = {
        "schema": "N26-sparse-stage-control-policy-v1",
        "semantic_replayer_file": "verify_conditional_force_stage.py",
        "acceptance_checker_file": "verify_conditional_force_stage_sparse.py",
        "angular_control_is_not_a_new_stage_payment": True,
    }
    (args.output / "MANIFEST.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"built": True, "verified": False,
                      "unchanged_exact_geometry_and_all_nine_controls_still_required": True,
                      "fresh_native_agreement_required": True}), flush=True)


if __name__ == "__main__":
    main()
