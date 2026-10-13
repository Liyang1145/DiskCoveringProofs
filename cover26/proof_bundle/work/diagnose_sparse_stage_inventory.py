"""Read-only input inventory diagnosis; no acceptance or geometry is credited."""

import argparse
from datetime import datetime
import json
from pathlib import Path

import verify_conditional_force_stage_sparse as sparse


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--area-bundle", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    values, _ = sparse.input_gate(args.input, args.area_bundle)
    paths = {
        sparse.exact.combinatorics.linux(path): sparse.exact.local_path(path)
        for path in values[-1]
    }
    own = args.input.resolve()
    local = []
    for text, path in paths.items():
        resolved = path.resolve()
        if resolved == own or own in resolved.parents:
            local.append({
                "path": text, "sha256_now": sparse.exact.sha(path),
                "modified": datetime.fromtimestamp(path.stat().st_mtime).isoformat(),
            })
    report = {
        "schema": "N26-sparse-stage-input-inventory-diagnosis-v1",
        "unique_input_dependencies": len(paths),
        "current_bundle_input_dependencies": local,
        "initial_inventory_must_not_include_later_generated_outputs": True,
        "verified_stage_geometry": False, "new_geometric_payments": 0,
    }
    args.report.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2), flush=True)


if __name__ == "__main__":
    main()
