"""Read-only final bundle audit, followed by a frozen local evidence inventory."""

import argparse
import json
from pathlib import Path

from audit_prefix_partition import WORK, check_frontier
from audit_prefix_origin import OriginReference
from new_upper_scope import sha as unnormalized_sha
from verify_rational_cover import verify


def sha(path):
    return unnormalized_sha(str(path).replace("\\", "/"))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    out = WORK.parent / "outputs"
    cover_folder = out / "n26-rational-upper-v1"
    scope_folder = out / "n26-new-scope-v1"
    frontier_folder = out / "n26-new-scope-frontiers-v1"
    reports = []
    for path in (cover_folder / "VERIFIED.json", scope_folder / "VERIFIED.json",
                 frontier_folder / "VERIFIED.json"):
        data = json.loads(path.read_text(encoding="utf-8"))
        if data["global_optimality_proved"]:
            raise ValueError("unexpected global completion claim")
        for dependency, digest in data["files"].items():
            if sha(dependency) != digest:
                raise ValueError("changed bound input: " + dependency)
        reports.append(data)
    geometry = json.loads((cover_folder / "geometry.json").read_text(encoding="utf-8"))
    cert = json.loads((cover_folder / "cover-certificate.json").read_text(encoding="utf-8"))
    if cert["geometry_sha256"] != sha(cover_folder / "geometry.json"):
        raise ValueError("unbound geometry")
    result = verify(geometry, cert)
    if result["radius"] != reports[0]["radius"]:
        raise ValueError("wrong reported upper radius")
    constants = json.loads((scope_folder / "CONSTANTS.json").read_text(encoding="utf-8"))
    families = []
    for entry in reports[2]["families"]:
        path = Path(entry["frontier_path"])
        if sha(path) != entry["frontier_sha256"]:
            raise ValueError("frontier changed")
        data = json.loads(path.read_text(encoding="utf-8"))
        reference = OriginReference(26, entry["B"], "dfs",
                                    caps=constants["angle_caps"], scale=constants["angle_scale"])
        rows = check_frontier(data, reference, (), 2)
        if len(rows) != entry["frontier_nodes"] or not data["origin_screen"]:
            raise ValueError("new frontier overclaimed")
        families.append({"B": entry["B"], "I": entry["I"], "frontier_nodes": len(rows)})
    inventory = [
        Path(__file__), out / "n26-STATUS.md", out / "n26-new-upper-and-scope-20261009.md",
        cover_folder / "geometry.json", cover_folder / "cover-certificate.json",
        cover_folder / "VERIFIED.json", scope_folder / "CONSTANTS.json",
        scope_folder / "DEPENDENCIES.json", scope_folder / "VERIFIED.json",
        frontier_folder / "VERIFIED.json",
    ]
    report = {
        "schema": "N26-new-upper-current-bundle-audit-v1",
        "current_bound_bytes_rechecked": True,
        "closed_unit_disk_upper_replayed": True,
        "rational_radius_upper": result["radius"],
        "external_n8_dependency_explicit": True,
        "new_family_frontiers_independently_reconstructed": families,
        "full_catalog_complete": False, "global_optimality_proved": False,
        "files": {str(path): sha(path) for path in inventory},
    }
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items() if key != "files"}, indent=2),
          flush=True)


if __name__ == "__main__":
    main()
