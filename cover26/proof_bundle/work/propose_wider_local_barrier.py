"""Reuse rational data from a bound local certificate at a wider proposed box."""

import argparse
import json
from pathlib import Path

from verify_local_barrier import sha


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--halfwidth", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    report = json.loads((args.source / "VERIFIED.json").read_text())
    if not report["verified"] or not report["strict_local_optimality_modulo_rotations_proved"]:
        raise ValueError("unaccepted source local certificate")
    for name, digest in report["files"].items():
        if sha(args.source / name) != digest:
            raise ValueError("changed source local data")
    proposal = json.loads((args.source / "CERTIFICATE.json").read_text())
    proposal["suggested_neighbourhood_halfwidth"] = args.halfwidth
    proposal["discovery_source_acceptance_sha256"] = sha(args.source / "VERIFIED.json")
    proposal["discovery_source_neighbourhood_halfwidth"] = report["neighbourhood_halfwidth"]
    args.output.write_text(json.dumps(proposal, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"verified": False, "suggested_neighbourhood_halfwidth": args.halfwidth}), flush=True)


if __name__ == "__main__":
    main()
