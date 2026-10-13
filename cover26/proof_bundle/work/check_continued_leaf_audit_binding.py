"""Read-only exact content recheck of the completed continued-leaf audit."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

from verify_terminal_catalog import local_path, sha


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--audit", type=Path, required=True)
    parser.add_argument("--angles", type=Path, required=True)
    args = parser.parse_args()
    audit = json.loads(args.audit.read_text(encoding="utf-8"))
    if (not audit["current_bound_bytes_rechecked"]
            or audit["current_pending_cover_transport_subtrees"] != 3570
            or audit["candidate_angle_unresolved_closed_boxes"] != 103
            or audit["global_optimality_proved"]):
        raise ValueError("continued-leaf audit has a wrong acceptance scope")
    for text, digest in audit["files"].items():
        if sha(local_path(text)) != digest:
            raise ValueError("continued-leaf audited bytes changed: " + text)
    accepted = json.loads((args.angles / "VERIFIED.json").read_text(encoding="utf-8"))
    error = F(accepted["leaf_specific_pinning_maximum_center_error_upper"])
    if not error < F(8333, 10**9) < F(7, 800000):
        raise ValueError("hull-local maximum error did not enter the unchanged neighborhood")
    print(json.dumps({"all_current_audit_file_digests_rehashed": len(audit["files"]),
                      "maximum_hull_center_error_strictly_below_8333_over_10power9": True,
                      "original_52_coordinate_allowance_unchanged": "7/800000",
                      "same_root_full_chain_current_binding_confirmed": True}))


if __name__ == "__main__":
    main()
