"""Exact centered polynomial interval evaluation for the unrestricted N26 box.

The existing local proof engine is kept byte-identical. Polynomial translation
is exact Fraction arithmetic; outward interval evaluation takes place only
after translation. This file and its base engine are both published.
"""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from math import comb
from pathlib import Path

import verify_local_barrier as base


GRID = 10**12
ORIGINAL_GATE = base.parameter_gate
ORIGINAL_EVALUATE = base.evaluate


def translate(poly, shift):
    dimension = len(shift)
    result = {}
    for exponent, coefficient in poly.items():
        terms = {(0,) * dimension: F(coefficient)}
        for j, degree in enumerate(exponent):
            if not degree:
                continue
            factors = [F(comb(degree, k)) * shift[j]**(degree - k) for k in range(degree + 1)]
            following = {}
            for e, c in terms.items():
                for k, factor in enumerate(factors):
                    if not factor:
                        continue
                    f = list(e)
                    f[j] += k
                    f = tuple(f)
                    following[f] = following.get(f, F(0)) + c * factor
            terms = following
        for e, c in terms.items():
            result[e] = result.get(e, F(0)) + c
    return {e: c for e, c in result.items() if c}


def nearest_integer(value):
    value = F(value)
    return (2 * value.numerator + value.denominator) // (2 * value.denominator)


class CenteredEvaluator:
    def __init__(self):
        self.cache = {}

    def __call__(self, poly, powers):
        if not poly:
            return base.ZERO
        if any(len(row) < 2 for row in powers):
            raise ValueError("centered evaluator missing variable intervals")
        mid_numerators = tuple(nearest_integer(F(row[1][0] + row[1][1], 2 * base.S) * GRID)
                               for row in powers)
        key = tuple(sorted(poly.items())), mid_numerators
        if key not in self.cache:
            shift = tuple(F(n, GRID) for n in mid_numerators)
            self.cache[key] = translate(poly, shift)
        shifted_box = [(row[1][0] - n * (base.S // GRID), row[1][1] - n * (base.S // GRID))
                       for row, n in zip(powers, mid_numerators)]
        shifted_powers = base.powers_for(shifted_box, [len(row) - 1 for row in powers])
        return ORIGINAL_EVALUATE(self.cache[key], shifted_powers)


def parameter_gate(proposal):
    delta = F(proposal["suggested_neighbourhood_halfwidth"])
    if not F(1, 10**12) <= delta <= F(1, 1000):
        raise ValueError("centered local box outside proved rotation/reference range")
    surrogate = deepcopy(proposal)
    surrogate["suggested_neighbourhood_halfwidth"] = str(min(delta, F(1, 10**6)))
    alpha, _, q = ORIGINAL_GATE(surrogate)
    if base.S % GRID:
        raise ValueError("translation grid is not exactly representable at interval scale")
    return alpha, delta, q


def source_gate(basis_folder, stress_folder, proposal):
    report_path = basis_folder / "VERIFIED.json"
    report = json.loads(report_path.read_text())
    if (not report["verified"] or not report["strict_local_optimality_modulo_rotations_proved"]
            or report["global_optimality_proved"]
            or proposal["discovery_source_acceptance_sha256"] != base.sha(report_path)):
        raise ValueError("centered local proposal is not bound to its accepted base certificate")
    for name, digest in report["files"].items():
        if base.sha(basis_folder / name) != digest:
            raise ValueError("accepted base local evidence changed")
    if base.sha(base.__file__) != report["files"]["verify_local_barrier.py"]:
        raise ValueError("centered verifier imported a different base proof engine")
    return base.source_gate(stress_folder, proposal)


def derive(original, root, records, proposal, progress=False):
    evaluator = CenteredEvaluator()
    old_gate, old_evaluate = base.parameter_gate, base.evaluate
    try:
        base.parameter_gate, base.evaluate = parameter_gate, evaluator
        result = base.derive(original, root, records, proposal, progress=progress)
    finally:
        base.parameter_gate, base.evaluate = old_gate, old_evaluate
    return {
        **result,
        "exact_rational_polynomial_translation_before_outward_evaluation": True,
        "translation_grid_denominator": str(GRID),
        "all_interval_domains_still_cover_entire_unrestricted_gauge_box": True,
        "rotation_reference_range_reproved_up_to_halfwidth": "1/1000",
    }


def translation_controls():
    for count in (2, 3):
        polynomial = base.template(count)
        shift = tuple(F((-1)**i * (i + 1), 100) for i in range(2 * count + 1))
        transformed = translate(polynomial, shift)
        if translate(transformed, tuple(-x for x in shift)) != polynomial:
            raise AssertionError("exact binomial translation does not invert")
        # Differentiation must commute with the exact change x = m + y.
        for j in range(2 * count + 1):
            if base.derivative(transformed, j) != translate(base.derivative(polynomial, j), shift):
                raise AssertionError("centered contact derivative identity failed")
    return {"exact_inverse_translation_controls": 2,
            "exact_translation_derivative_commutation_controls": 12}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--basis", type=Path, required=True)
    parser.add_argument("--stress", type=Path, required=True)
    parser.add_argument("--proposal", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    proposal = json.loads(args.proposal.read_text())
    original, root, records = source_gate(args.basis, args.stress, proposal)
    controls = translation_controls()
    print(json.dumps({"centered_interval_box_check_started": True,
                      "halfwidth": proposal["suggested_neighbourhood_halfwidth"]}), flush=True)
    result = derive(original, root, records, proposal, progress=True)
    negatives = []

    def reject(label, fn):
        try:
            fn()
        except (ValueError, KeyError, TypeError):
            negatives.append(label)
        else:
            raise AssertionError("bad centered local certificate accepted: " + label)

    bad = deepcopy(proposal)
    bad["contacts"].pop()
    reject("omitted-positive-contact", lambda: source_gate(args.basis, args.stress, bad))
    bad = deepcopy(proposal)
    bad["generic_raw_contact_polynomials"]["3"][0]["coefficient"] = "100"
    reject("changed-contact-polynomial", lambda: parameter_gate(bad))
    bad = deepcopy(proposal)
    bad["gauge_dimension"] = 13
    reject("D2-only-perturbation-domain", lambda: parameter_gate(bad))
    bad = deepcopy(proposal)
    bad["suggested_neighbourhood_halfwidth"] = "1/100"
    reject("box-exceeds-proved-rotation-range", lambda: parameter_gate(bad))
    bad = deepcopy(proposal)
    bad["suggested_neighbourhood_halfwidth"] = "1/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"
    reject("box-too-small-to-contain-certified-root-reference", lambda: parameter_gate(bad))
    bad = deepcopy(proposal)
    bad["chosen"]["preconditioner_numerators"] = [["0"] * 51 for _ in range(51)]
    reject("zero-preconditioner", lambda: derive(original, root, records, bad))
    bad = deepcopy(proposal)
    bad["stress_acceptance_sha256"] = "0" * 64
    reject("unbound-first-order-equilibrium", lambda: source_gate(args.basis, args.stress, bad))
    args.output.mkdir(parents=True)
    (args.output / "CERTIFICATE.json").write_bytes(args.proposal.read_bytes())
    (args.output / "verify_centered_local_barrier.py").write_bytes(Path(__file__).read_bytes())
    (args.output / "verify_local_barrier.py").write_bytes(Path(base.__file__).read_bytes())
    proof = Path(__file__).with_name("n26-centered-local-barrier-proof.md")
    if not proof.exists():
        proof = Path(__file__).with_name("PROOF.md")
    (args.output / "PROOF.md").write_bytes(proof.read_bytes())
    files = ["CERTIFICATE.json", "verify_centered_local_barrier.py", "verify_local_barrier.py", "PROOF.md"]
    report = {
        "schema": "N26-centered-unrestricted-exact-polynomial-local-lower-v1",
        "verified": True, **result,
        "same_root_entire_disk_cover_already_proved": True,
        "local_optimality_proved": True, "global_optimality_proved": False,
        "formal_machine_geometry_proof": False,
        "proof_scope": "Specified same-root labelled candidate, all center coordinates independently variable modulo overall rotation",
        "translation_positive_controls": controls,
        "negative_controls_rejected": negatives,
        "basis_source_acceptance_sha256": base.sha(args.basis / "VERIFIED.json"),
        "stress_acceptance_sha256": base.sha(args.stress / "VERIFIED.json"),
        "files": {name: base.sha(args.output / name) for name in files},
    }
    (args.output / "VERIFIED.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items() if key != "files"}, indent=2), flush=True)


if __name__ == "__main__":
    main()
