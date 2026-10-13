"""Pure product-forest controls, with no typed diagnostic model/source import."""

from copy import deepcopy
from fractions import Fraction as F

import n26_difference_product_candidate_forest as forest


def controls(original, kernel, arcs, row, nodes):
    leaves = forest.partition(original["matrix"], row, nodes, forest.independently_contract, True)
    energy = next(leaf for leaf in leaves if leaf["kind"] == "PRODUCT-ENERGY")
    local = next(leaf for leaf in leaves if leaf["kind"] == "LOCAL")
    certificate = nodes[energy["index"]]["certificate"]
    rejected = []

    def reject(label, call):
        try:
            call()
        except (ValueError, KeyError, TypeError, IndexError):
            rejected.append(label)
        else:
            raise AssertionError("invalid actual product-forest control accepted: " + label)

    def changed_partition(mutation):
        bad = deepcopy(nodes)
        mutation(bad)
        forest.partition(original["matrix"], row, bad, forest.independently_contract, True)

    split_index = next(index for index, node in enumerate(nodes) if node["kind"] == "SPLIT")
    reject("actual-root-one-closed-half-omitted", lambda: changed_partition(
        lambda bad: bad[split_index].update(children=bad[split_index]["children"][:1])))
    reject("actual-root-shared-half-identified", lambda: changed_partition(
        lambda bad: bad[split_index].update(children=[bad[split_index]["children"][0]] * 2)))
    reject("actual-root-unreachable-hidden-node", lambda: changed_partition(
        lambda bad: bad.append({"kind": "OPEN"})))
    reject("actual-root-nonempty-energy-region-called-EMPTY", lambda: changed_partition(
        lambda bad: bad.__setitem__(energy["index"], {"kind": "EMPTY"})))
    reject("actual-root-unsupported-curvature-mode", lambda: changed_partition(
        lambda bad: bad.__setitem__(energy["index"], {"kind": "UNPROVED-PRODUCT"})))
    reject("actual-root-split-has-unknown-payment-fields", lambda: changed_partition(
        lambda bad: bad[split_index].update(fake_payment=True)))

    def changed_energy(mutation):
        bad = deepcopy(certificate)
        mutation(bad)
        forest.product.bound(
            kernel, original["matrix"], energy["lower"], energy["upper"],
            bad, original["radius"], arcs)

    reject("actual-energy-negative-product-multiplier", lambda: changed_energy(
        lambda bad: bad["products"][0].update(multiplier="-1")))
    reject("actual-energy-missing-reference-linear-product-definition", lambda: changed_energy(
        lambda bad: bad["products"][0].pop("second_constraint")))
    reject("actual-energy-duplicate-slack-product", lambda: changed_energy(
        lambda bad: bad["products"].append(deepcopy(bad["products"][0]))))
    reject("actual-energy-all-products-omitted", lambda: changed_energy(
        lambda bad: bad.update(products=[])))
    reject("actual-energy-nonpositive-corrected-curvature", lambda: changed_energy(
        lambda bad: bad.update(signed_eta=["-100000000000000000000"] * 15)))
    reject("actual-energy-unknown-certificate-proof-field", lambda: changed_energy(
        lambda bad: bad.update(reference_product_constant_falsely_zero=True)))
    reject("actual-LOCAL-full-root-substituted-for-closed-leaf", lambda:
           forest.original_forest.local_proof(
               original, list(map(F, row["sharp_lower"])), list(map(F, row["sharp_upper"]))))

    local_result = forest.original_forest.local_proof(
        original, list(map(F, local["lower"])), list(map(F, local["upper"])))
    if F(local_result["strict_original_LOCAL_entry_margin"]) <= 0:
        raise AssertionError("actual product-forest LOCAL has no original strict entry margin")
    tiny = [tuple(map(F, pair))
            for pair in original["cap"]["known_candidate_tiny_angle_cells"]]
    tiny_box = forest.tighten(original["matrix"], [a for a, _ in tiny], [c for _, c in tiny])
    tiny_result = forest.product.bound(
        kernel, original["matrix"], *tiny_box, certificate, original["radius"], arcs)
    if tiny_result["arithmetic_strict_target_test_passed"]:
        raise AssertionError("product certificate excludes the known feasible tiny candidate")
    return rejected, {
        "original_LOCAL_closed_leaf_replayed": True,
        "original_LOCAL_result": local_result,
        "known_feasible_tiny_candidate_not_strictly_excluded": True,
        "tiny_candidate_arithmetic_result": tiny_result,
    }
