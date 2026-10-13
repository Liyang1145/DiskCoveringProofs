# Signed Taylor bounds with NEW positive original-rod supports

The rod geometry remains the original 92-edge, 62-vertex graph with 16
anchors and 46 grounded free vertices. The positive weights and grounded
inverse are NEW and must never be labelled as the original fixed kernel.
`n26_alternative_signed_hull_energy.py` checks an exact original edge match,
positive weights, a fresh integer inverse, harmonic coefficients and Schur
identities through the separate alternative-support gate.

The unchanged generic Hessian minorant, outward point/gradient rounding and
piecewise signed coordinate minima apply to any such positive Schur support.
No original-fixed-kernel identity flag is supplied or forged.

For a feasible rational reference r and a closed target box intersected with
the necessary difference polytope, bound the entire reference-to-target hull.
The exact matrix test is

    M + diag(eta) - (15/10^40) I > 0.

Exact positive LDL and full rational reconstruction prove the signed Taylor
lower bound. Point energy and gradient use outward 10^-80 rounding. Any
nonnegative difference-constraint dual is charged with its exact reference
constant and divergence. The final energy cap uses the NEW positive weight
sum and scale, and the unchanged exact Rstar upper endpoint. Conversion to
radius is outward by exact integer square root.

Numerical optimization only proposes weights, diagonals and duals. Its
success/convergence is not evidence. The actual exact inverse, positive LDL,
closed-domain reconstruction and strict energy/radius margins are evidence.

The new adaptive forests retain every previous non-OPEN node and positive
support exactly. Both closed halves and shared cut boundaries are rebuilt
with independent BFS/DFS difference contractions. Every strict leaf is
recomputed; remaining OPEN leaves are retained. The original LOCAL allowance
7/800000 and equality feasibility are not changed.

These modules currently provide UNADMITTED arithmetic evidence only.
The fixed arithmetic resource is DATA, not a current/source/history cache.
Neither the running two-mode mixed checker nor the tested product-only
checker accepts this NEW support mode. Whole-root closure, a distinct frozen
geometry interface, complete latest source/model/history replay, actual
publication replay, complete-current admission and independent final rehash
are still required. Global catalogue completeness and optimality remain open.
