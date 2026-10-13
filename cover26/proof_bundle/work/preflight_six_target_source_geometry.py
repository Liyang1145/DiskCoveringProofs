"""Read-only input/scope preflight; does NOT execute the geometry main."""

import argparse
import json
from pathlib import Path
import sys


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    args = parser.parse_args()
    sys.path.insert(0, str(args.input.resolve()))
    import verify_six_target_source_geometry as checker
    manifest, parent, source, layer = checker.input_gate(args.input)
    checker.previous.family_gate(args.input, manifest, parent)
    checker.controls_gate(args.input, source, manifest)
    print(json.dumps({
        "read_only_six_target_input_preflight_passed": True,
        "actual_completed_parent_dependencies": len(parent["files"]),
        "actual_source_prefixes": len(source["pending_states"]),
        "actual_candidate_whole_roots": layer["actual_remaining_candidate_whole_roots"],
        "full_geometry_main_NOT_executed": True,
        "new_formal_geometric_payments": 0,
    }), flush=True)


if __name__ == "__main__":
    main()
