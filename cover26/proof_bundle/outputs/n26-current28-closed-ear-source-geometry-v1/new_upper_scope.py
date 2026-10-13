"""New N26 family budget, conditional on an explicit published N8 theorem.

The N26 upper certificate is rechecked with exact rational arithmetic. The N8
theorem is a cited external mathematical dependency, not re-proved by this code.
"""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

from verify_rational_cover import verify as replay_cover


WORK = Path(__file__).resolve().parent
ROOT = WORK.parent
ARCHIVE = Path("C:/热爱单机但萌新/_incoming-local-math-20261004/recovered-20261004/workspace/research-2026")
ARCS = ARCHIVE / "disk-cover-proof-library/external/pinned/cover20/proof_bundle/core/exact_arcs.py"
PAPER = ARCHIVE / "disk-cover-proof-library/papers/fejes-toth-2005-n8-n10.pdf"
EXPECTED_PAPER = "29ca1999cc706747658082c0e459da78fda62ec356d6277a4f16b4878bd16917"


def local_path(text):
    if sys.platform == "win32" and text.startswith("/mnt/"):
        return Path(text[5].upper() + ":" + text[6:])
    if sys.platform != "win32" and len(text) > 2 and text[1] == ":":
        return Path("/mnt/" + text[0].lower() + text[2:])
    return Path(text)


def sha(path):
    return hashlib.sha256(local_path(str(path)).read_bytes()).hexdigest()


def publish(path, obj):
    if path.exists():
        raise FileExistsError(path)
    path.write_text(json.dumps(obj, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def load_arcs():
    spec = importlib.util.spec_from_file_location("new_n26_exact_arcs", local_path(str(ARCS)))
    arcs = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(arcs)
    return arcs


def select_caps(U, arcs):
    D = 10**7
    caps = []
    for k in range(1, 5):
        lo, hi = 0, D // 2
        while hi - lo > 1:
            mid = (lo + hi) // 2
            lower = F(arcs.sincos_turn(F(mid, 2 * D))[1][0], arcs.SCALE)
            if lower > k * U:
                hi = mid
            else:
                lo = mid
        caps.append(hi)
    return caps


def gate(constants, upper, arcs):
    U = F(constants["radius_upper"])
    if constants["N"] != 26 or U != F(upper["radius"]):
        raise ValueError("wrong order or unbound upper threshold")
    if not upper["verified"] or not upper["continuous_cover_proved"]:
        raise ValueError("upper lacks continuous certificate")
    if not 0 < U < F(1, 4):
        raise ValueError("threshold outside domain")
    if constants["external_n8_theorem_assumed"] is not True or constants["n8_reproved_here"]:
        raise ValueError("incorrect imported-theorem scope")
    if constants["source_pdf_sha256"] != EXPECTED_PAPER or sha(PAPER) != EXPECTED_PAPER:
        raise ValueError("unbound published source")
    D, caps = constants["angle_scale"], constants["angle_caps"]
    if D != 10**7 or len(caps) != 4 or not 0 < caps[0] < caps[1] < caps[2] < caps[3] < D // 2:
        raise ValueError("invalid angular caps")
    margins = [
        F(arcs.sincos_turn(F(cap, 2 * D))[1][0], arcs.SCALE) - k * U
        for k, cap in enumerate(caps, 1)
    ]
    if min(margins) <= 0:
        raise ValueError("nonpositive sine margin")
    boundary_gap = F(arcs.sincos_turn(F(1, 26))[1][0], arcs.SCALE) - U
    if boundary_gap <= 0 or D - 13 * caps[0] <= 0:
        raise ValueError("minimum boundary count not established")
    cos_interval = arcs.sincos_turn(F(1, 7))[0]
    chi = F(cos_interval[1], arcs.SCALE)
    published_n8_radius_lower = 1 / (1 + 2 * chi)
    conservative_n8_lower = F(443, 1000)
    if published_n8_radius_lower <= conservative_n8_lower:
        raise ValueError("rational N8 lower not justified by imported formula")
    q = U / (1 - 2 * U)
    if q >= conservative_n8_lower:
        raise ValueError("eight inner disks not excluded")
    families = [[b, 26 - b] for b in range(14, 18)]
    if not (constants["minimum_boundary_cells"] == 14
            and constants["minimum_interior_cells"] == 9
            and constants["maximum_boundary_cells"] == 17
            and constants["families"] == families):
        raise ValueError("wrong necessary family list")
    return {
        "positive_exact_sine_margins": list(map(str, margins)),
        "direct_boundary_sine_gap": str(boundary_gap),
        "integer_circle_budget_gap": D - 13 * caps[0],
        "cos_2pi_over7_interval": list(map(str, map(lambda v: F(v, arcs.SCALE), cos_interval))),
        "imported_n8_radius_rational_lower": str(published_n8_radius_lower),
        "conservative_n8_lower_used": str(conservative_n8_lower),
        "imported_theorem_to_rational_lower_gap": str(published_n8_radius_lower - conservative_n8_lower),
        "normalized_core_radius_upper": str(q),
        "strict_n8_core_gap": str(conservative_n8_lower - q),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    folder = ROOT / "outputs/n26-rational-upper-v1"
    upper_path = folder / "VERIFIED.json"
    upper = json.loads(upper_path.read_text(encoding="utf-8"))
    for path, digest in upper["files"].items():
        if sha(path) != digest:
            raise ValueError("changed upper-bound evidence")
    geometry_path, cert_path = folder / "geometry.json", folder / "cover-certificate.json"
    geometry = json.loads(geometry_path.read_text(encoding="utf-8"))
    certificate = json.loads(cert_path.read_text(encoding="utf-8"))
    if certificate["geometry_sha256"] != sha(geometry_path):
        raise ValueError("unbound geometry")
    fresh_upper = replay_cover(geometry, certificate)
    if fresh_upper["radius"] != upper["radius"]:
        raise ValueError("current upper replay disagrees")
    arcs = load_arcs()
    U = F(upper["radius"])
    constants = {
        "schema": "N26-own-new-upper-family-budget-v1",
        "N": 26, "radius_upper": str(U), "angle_scale": 10**7,
        "angle_caps": select_caps(U, arcs),
        "minimum_boundary_cells": 14, "minimum_interior_cells": 9,
        "maximum_boundary_cells": 17,
        "families": [[14, 12], [15, 11], [16, 10], [17, 9]],
        "external_n8_theorem_assumed": True, "n8_reproved_here": False,
        "source_pdf_sha256": EXPECTED_PAPER,
        "global_optimality_proved": False,
    }
    results = gate(constants, upper, arcs)
    negatives = []
    for label, field, value in (
        ("wrong-order", "N", 25),
        ("old-upper-not-new-certificate", "radius_upper", "239146311738101/1000000000000000"),
        ("eight-internal-claim", "minimum_interior_cells", 8),
        ("unpaid-B18-reintroduced", "maximum_boundary_cells", 18),
        ("missing-family", "families", [[14, 12], [16, 10], [17, 9]]),
        ("unbound-source", "source_pdf_sha256", "0" * 64),
        ("hidden-external-assumption", "external_n8_theorem_assumed", False),
        ("false-n8-reproof", "n8_reproved_here", True),
    ):
        wrong = deepcopy(constants)
        wrong[field] = value
        try:
            gate(wrong, upper, arcs)
        except (ValueError, KeyError):
            negatives.append(label)
        else:
            raise AssertionError("incorrect family budget accepted: " + label)
    wrong = deepcopy(constants)
    wrong["angle_caps"][3] -= 1
    try:
        gate(wrong, upper, arcs)
    except ValueError:
        negatives.append("too-small-eight-rod-cap")
    else:
        raise AssertionError("non-strict eight-rod cap accepted")
    args.output.mkdir(parents=True)
    publish(args.output / "CONSTANTS.json", {**constants, **results})
    dependencies = {
        "schema": "N26-explicit-imported-n8-dependency-v1",
        "author": "G. Fejes Tóth",
        "title": "Thinnest Covering of a Circle by Eight, Nine, or Ten Congruent Circles",
        "publication": "MSRI Publications 52 (2005), 361–376",
        "source_url": "https://library.slmath.org/books/Book52/files/18fejes.pdf",
        "source_pdf": str(PAPER), "source_pdf_sha256": EXPECTED_PAPER,
        "theorem_used": "r_D(8) >= 1/(1+2*cos(2*pi/7))",
        "weaker_rational_lower_used": "443/1000",
        "n8_reproved_here": False,
        "scope_note": "The published radius conclusion is imported explicitly. The accompanying center-distance coordinate statement has a sin/cos inconsistency; no construction coordinates or uniqueness claim are used.",
    }
    publish(args.output / "DEPENDENCIES.json", dependencies)
    publish(args.output / "VERIFIED.json", {
        "schema": "N26-new-upper-family-scope-audit-v1",
        "arithmetic_verified": True,
        "N26_continuous_upper_replayed": True,
        "family_scope_valid_assuming_cited_n8_theorem": True,
        "N8_lower_bound_reproved_here": False,
        "B18_removed_from_new_strict_counterexample_scope": True,
        "old_B18_enumeration_completed": False,
        "families": constants["families"],
        "global_optimality_proved": False,
        "negative_controls_rejected": negatives,
        "files": {str(path): sha(path) for path in (
            Path(__file__), WORK / "verify_rational_cover.py", ARCS, PAPER,
            upper_path, geometry_path, cert_path,
            args.output / "CONSTANTS.json", args.output / "DEPENDENCIES.json")},
    })
    print(json.dumps({"new_radius_upper": str(U), "angle_caps": constants["angle_caps"],
                      "minimum_interior_cells": 9, "families": constants["families"],
                      "strict_n8_core_gap": results["strict_n8_core_gap"],
                      "external_n8_theorem_assumed": True,
                      "negative_controls": len(negatives)}, indent=2), flush=True)


if __name__ == "__main__":
    main()
