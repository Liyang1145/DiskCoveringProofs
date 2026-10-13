"""Build a root-containing angular hull of specified retained candidate boxes."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

import verify_anchor_pinning as base


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--basis", type=Path, required=True)
    parser.add_argument("--local", type=Path, required=True)
    parser.add_argument("--partition", type=Path, required=True)
    parser.add_argument("--target-indices", default="97,98,99,100")
    parser.add_argument("--include-transport-cells", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    base.checked_bundle(args.basis)
    base.checked_bundle(args.local)
    partition, _ = base.checked_bundle(args.partition)
    proposal = json.loads((args.basis / "CERTIFICATE.json").read_text())
    pending = json.loads((args.partition / "PENDING-ANGLES.json").read_text())
    indices = sorted(set(map(int, args.target_indices.split(","))))
    rows = [r for r in pending if r["index"] in indices]
    if sorted(r["index"] for r in rows) != indices:
        raise ValueError("target angular boxes are not all retained OPEN leaves")
    cells = [list(map(F, r)) for r in proposal["closed_anchor_angle_cells"]]
    for row in rows:
        for i, (lo, hi) in enumerate(zip(row["lower"], row["upper"])):
            cells[i][0] = min(cells[i][0], F(lo))
            cells[i][1] = max(cells[i][1], F(hi))
    if args.include_transport_cells is not None:
        base.checked_bundle(args.include_transport_cells, absolute=True)
        if base.sha(args.include_transport_cells / "VERIFIED.json") != proposal["source_acceptance_sha256"]["transport"]:
            raise ValueError("broader transport cells come from a different accepted covering root")
        transport_cells = json.loads((args.include_transport_cells / "CANDIDATE-PATH.json").read_text())[
            "exact_rotated_anchor_cells"]
        for i, (lo, hi) in enumerate(transport_cells):
            cells[i][0] = min(cells[i][0], F(lo))
            cells[i][1] = max(cells[i][1], F(hi))
        proposal["discovery_all_coarse_transport_anchor_cells_included"] = True
    proposal["closed_anchor_angle_cells"] = [list(map(str, row)) for row in cells]
    proposal["source_acceptance_sha256"]["local"] = base.sha(args.local / "VERIFIED.json")
    proposal["refinement_basis_acceptance_sha256"] = base.sha(args.basis / "VERIFIED.json")
    proposal["discovery_partition_acceptance_sha256"] = base.sha(args.partition / "VERIFIED.json")
    proposal["discovery_target_OPEN_indices"] = indices
    args.output.write_text(json.dumps(proposal, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"verified": False, "target_OPEN_indices": indices,
                      "maximum_angle_cell_width": str(max(hi - lo for lo, hi in cells))}), flush=True)


if __name__ == "__main__":
    main()
