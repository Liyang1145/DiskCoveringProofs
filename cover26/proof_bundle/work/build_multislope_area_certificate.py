"""Propose exact envelope tables and rationalized boundary LP duals."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

from verify_multislope_area import C, CAPS, D, SLOPES, case_boundary_bound, derive_tables
import verify_degree_area as base


WORK = Path(__file__).resolve().parent


def upper_integer(value):
    scaled = value * C
    return -((-scaled.numerator) // scaled.denominator) + 1


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    original = WORK.parent / "outputs/n26-degree-area-lower-v1"
    report = json.loads((original / "VERIFIED.json").read_text())
    for name, digest in report["files"].items():
        if base.sha(original / name) != digest:
            raise ValueError("changed base area evidence")
    proposals = json.loads((WORK / "n26-multislope-area-proposals-v1.json").read_text())
    if (proposals["source_graph_ledger_sha256"] != base.sha(original / "GRAPH-LEDGER.json")
            or proposals["source_profile_ledger_sha256"] != base.sha(original / "PROFILE-LEDGER.json")
            or tuple(map(F, proposals["slopes"])) != SLOPES):
        raise ValueError("unbound numerical proposal")
    old_cert = json.loads((original / "CERTIFICATE.json").read_text())
    arcs, _ = base.load_trig(original)
    maxima = derive_tables(old_cert, arcs, progress=True)
    cert = {
        "schema": "N26-area-graph-angle-rational-dual-proposal-v1",
        "N": 26, "slopes": list(map(str, SLOPES)), "coefficient_scale": C,
        "angle_scale": D, "caps": list(CAPS),
        "boundary_intercept_upper_integers": [
            [upper_integer(value) for value in row] for row in maxima],
        "graph_to_case": proposals["graph_to_case"],
        "full_catalog_complete": False, "global_optimality_proved": False}
    cases = []
    q = 10**12
    for proposed in proposals["cases"]:
        b = proposed["B"]
        supports = b * len(SLOPES)
        weights = {row: F(round(F(str(value)) * q), q)
                   for row, value in proposed["dual_nonzero_proposals"] if value > 0}
        for i in range(b):
            indices = [row for row in weights if row < supports and row // len(SLOPES) == i]
            total = sum((weights[row] for row in indices), F(0))
            if total <= 0:
                raise ValueError("proposal omits an auxiliary variable")
            for row in indices:
                weights[row] /= total
        case = {
            "B": b, "boundary_degrees": proposed["boundary_degrees"],
            "angle_constraints": proposed["angle_constraints"],
            "rational_dual_weights": [[row, str(value)] for row, value in sorted(weights.items()) if value > 0]}
        case["boundary_upper_rational"] = str(case_boundary_bound(case, cert))
        cases.append(case)
    args.output.mkdir(parents=True)
    for name in report["files"]:
        target = args.output / ("BASE-PROOF.md" if name == "PROOF.md" else name)
        target.write_bytes((original / name).read_bytes())
    base_report_path = args.output / "BASE-ACCEPTANCE.json"
    base_report_path.write_bytes((original / "VERIFIED.json").read_bytes())
    case_path = args.output / "CASE-CERTIFICATES.json"
    case_path.write_text(json.dumps(cases, indent=2) + "\n", encoding="utf-8")
    cert["base_acceptance_sha256"] = base.sha(base_report_path)
    cert["case_certificates_sha256"] = base.sha(case_path)
    (args.output / "MULTISLOPE-CERTIFICATE.json").write_text(json.dumps(cert, indent=2) + "\n", encoding="utf-8")
    for source, name in (
        (WORK / "verify_multislope_area.py", "verify_multislope_area.py"),
        (WORK / "n26-multislope-area-proof.md", "PROOF.md")):
        (args.output / name).write_bytes(source.read_bytes())
    (args.output / "BUILT-MULTISLOPE.json").write_text(json.dumps({
        "verified": False, "builder_sha256": base.sha(__file__),
        "global_optimality_proved": False}, indent=2) + "\n")
    print(json.dumps({"built": True, "verified": False, "boundary_LP_cases": len(cases)}), flush=True)


if __name__ == "__main__":
    main()
