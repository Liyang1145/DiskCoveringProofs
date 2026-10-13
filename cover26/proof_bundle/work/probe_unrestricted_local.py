"""Untrusted full 52-coordinate stress/curvature exploration at the exact root.

No D2 restriction is applied to perturbations. Floating matrices are discovery
only; none of these results are local or global optimality certificates.
"""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

import numpy as np
from scipy.linalg import null_space
from scipy.optimize import linprog

from moving_vertex_search import components, values_gradients


WORK = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    folder = WORK.parent / "outputs/n26-same-root-cover-v2"
    system = json.loads((folder / "SYSTEM.json").read_text())
    root = json.loads((folder / "ROOT-CERTIFICATE.json").read_text())
    point = [float(F(int(n), int(root["Qx"]))) for n in root["xnum"]]
    centers = np.array([[0 if item["variable"] is None else
                         item["sign"] * point[item["variable"]] for item in row]
                        for row in system["center_map"]])
    desc = components(centers)
    values, all_gradients = values_gradients(centers, desc)
    t = point[13]
    selected = np.flatnonzero(t - values < 1e-10)
    gradients = all_gradients[selected]
    m = len(selected)
    # Maximize the minimum nonnegative physical stress weight; boundary zero
    # weights and flat modes are recorded, not swept into a positive result.
    objective = np.r_[np.zeros(m), -1.]
    equalities = np.column_stack((np.vstack((gradients.T, np.ones(m))), np.zeros(53)))
    inequalities = np.column_stack((-np.eye(m), np.ones(m)))
    lp = linprog(objective, A_ub=inequalities, b_ub=np.zeros(m),
                 A_eq=equalities, b_eq=np.r_[np.zeros(52), 1.],
                 bounds=[(0., None)] * (m + 1), method="highs")
    if not lp.success:
        raise ValueError("no floating balanced stress proposal")
    weights = lp.x[:m]
    positive = np.flatnonzero(weights > 1e-8)
    zero = np.flatnonzero(weights <= 1e-8)
    hessian = np.zeros((52, 52))
    eps = 2e-6
    gradient_errors = []
    for j in range(52):
        plus, minus = centers.ravel().copy(), centers.ravel().copy()
        plus[j] += eps
        minus[j] -= eps
        vp, gp = values_gradients(plus.reshape(26, 2), desc)
        vm, gm = values_gradients(minus.reshape(26, 2), desc)
        gradient_errors.append(float(np.max(np.abs((vp - vm) / (2 * eps) - all_gradients[:, j]))))
        hessian[:, j] = weights @ ((gp[selected] - gm[selected]) / (2 * eps))
    asymmetry = float(np.max(np.abs(hessian - hessian.T)))
    hessian = (hessian + hessian.T) / 2
    rotation = np.column_stack((-centers[:, 1], centers[:, 0])).ravel()
    # Remove the rotational gauge only, not reflection-breaking perturbations.
    tangent = null_space(np.vstack((gradients[positive], rotation)))
    eigenvalues, vectors = np.linalg.eigh(tangent.T @ hessian @ tangent)
    negative_modes = []
    for index in np.flatnonzero(eigenvalues < -1e-7):
        vector = tangent @ vectors[:, index]
        derivatives = gradients[zero] @ vector
        negative_modes.append({
            "eigenvalue": float(eigenvalues[index]),
            "zero_stress_first_derivatives": derivatives.tolist(),
            "either_sign_first_order_critical": bool(np.all(derivatives <= 1e-8)
                                                    or np.all(derivatives >= -1e-8)),
            "full_coordinate_direction": vector.tolist()})
    # Report singular values separately from the threshold used for discovery.
    result = {
        "schema": "N26-unrestricted-floating-local-stress-curvature-probe-v1",
        "verified": False, "center_coordinates": 52, "D2_perturbation_restriction": False,
        "regular_component_count": len(values), "active_component_count": m,
        "stress_weights": weights.tolist(), "active_component_indices": selected.tolist(),
        "minimum_weight_proposal": float(lp.x[-1]),
        "gradient_balance_infinity_residual": float(np.max(np.abs(gradients.T @ weights))),
        "stress_sum_residual": float(abs(weights.sum() - 1)),
        "positive_stress_components": len(positive), "zero_stress_components": len(zero),
        "active_gradient_singular_values": np.linalg.svd(gradients, compute_uv=False).tolist(),
        "positive_gradient_tangent_dimension_after_rotation": tangent.shape[1],
        "weighted_hessian_symmetry_error": asymmetry,
        "analytic_gradient_finite_difference_error": max(gradient_errors),
        "weighted_tangent_hessian_eigenvalues": eigenvalues.tolist(),
        "negative_modes": negative_modes,
        "local_optimality_proved": False, "global_optimality_proved": False}
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: result[key] for key in (
        "verified", "active_component_count", "minimum_weight_proposal",
        "gradient_balance_infinity_residual", "positive_stress_components",
        "zero_stress_components", "positive_gradient_tangent_dimension_after_rotation",
        "weighted_tangent_hessian_eigenvalues", "local_optimality_proved")}), flush=True)


if __name__ == "__main__":
    main()
