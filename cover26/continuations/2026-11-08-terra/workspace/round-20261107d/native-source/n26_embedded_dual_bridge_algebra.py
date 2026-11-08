"""Universal algebra for straight clipped duals and corner-starred limits."""

import sympy as sp

import n26_unit_cap_universal_identities as sparse


SCHEMA = "N26-universal-empty-circle-and-corner-stellar-bridge-algebra-v1"
VARIABLES = (
    "ax", "ay", "bx", "by", "cx", "cy", "dx", "dy",
    "qx", "qy", "t", "s", "k", "epsilon", "u", "v",
)
HYPOTHESES = (
    "cover-input:0<=r<rho<same-excluded-radius<U=234701/1000000",
    "original-subcover:distinct-generic-centers-strictly-inside-D",
    "original-subcover:irredundant-and-clipped-boundary-ownership-does-not-return",
    "crossing-only:0<t<1-and-0<s<1-and-(1-t)*a+t*b=(1-s)*c+s*d",
    "empty-circle-only:f(a)=f(b)=0-and-f(c)>0-and-f(d)>0",
    "reverse-empty-circle-only:g(c)=g(d)=0-and-g(a)>0-and-g(b)>0",
    "starring-only:0<epsilon<1/2-and-original-center-triangle-oriented-nondegenerately",
    "starring-limit-only:epsilon-tends-to-zero-and-new-label-copies-one-OLD-corner",
    "common-witness-only:0<=u-and-0<=v-and-u+v<=1",
    "original-cell-areas-retained-and-shadow-cell-areas-zero",
    "B-is-original-irredundant-subcover-owner-count-NOT-new-shadow-nearest-diagram-count",
)
SCOPE = (
    "symbolic-identities-NOT-finite-cover-samples",
    "noncrossing-from-TWO-strict-empty-circles-and-written-ordered-real-contradiction",
    "cyclic-normal-order-and-disk-dual-topology-are-explicit-written-arguments",
    "shadow-labels-may-coincide-with-old-physical-centers",
    "embedding-is-a-limit-of-proper-interior-stellar-drawings",
    "common-parent-witnesses-remain-valid-by-convexity",
    "degree-area-uses-at-most-vertex-budgets-not-26-fictional-positive-area-cells",
    "NOT-complete-current-source-replay-or-final-unrestricted-joint-acceptance",
)


def expressions():
    variables = sp.symbols(" ".join(VARIABLES), real=True)
    ax, ay, bx, by, cx, cy, dx, dy, qx, qy, t, s, k, epsilon, u, v = variables
    a, b, c, d, q = (sp.Matrix(coords) for coords in (
        (ax, ay), (bx, by), (cx, cy), (dx, dy), (qx, qy)))

    def norm(point):
        return point.dot(point)

    def orient(first, second, third):
        left, right = second-first, third-first
        return left[0]*right[1]-left[1]*right[0]

    def circle(point):
        return norm(point)-2*q.dot(point)+k

    pab, pcd = (1-t)*a+t*b, (1-s)*c+s*d
    aa, cc = t*(1-t)*norm(a-b), s*(1-s)*norm(c-d)
    stellar, delta = (1-2*epsilon)*a+epsilon*b+epsilon*c, orient(a, b, c)
    bary = (1-u-v)*a+u*b+v*c
    differences = (1-u-v)*u*norm(a-b)+(1-u-v)*v*norm(a-c)+u*v*norm(b-c)
    identities = {
        "ab-weighted-squared-norm": ((1-t)*norm(a)+t*norm(b), norm(pab)+aa),
        "cd-weighted-squared-norm": ((1-s)*norm(c)+s*norm(d), norm(pcd)+cc),
        "ab-weighted-circle": ((1-t)*circle(a)+t*circle(b), circle(pab)+aa),
        "cd-weighted-circle": ((1-s)*circle(c)+s*circle(d), circle(pcd)+cc),
        "crossing-circle-gap": (
            (1-s)*circle(c)+s*circle(d)-(1-t)*circle(a)-t*circle(b)-cc+aa,
            (pcd[0]-pab[0])*(pcd[0]+pab[0]-2*qx)
            +(pcd[1]-pab[1])*(pcd[1]+pab[1]-2*qy)),
        "nearest-site-bisector-normal": (
            norm(q-a)-norm(q-b), 2*(b-a).dot(q)+norm(a)-norm(b)),
        "stellar-child-ab": (orient(a, b, stellar), epsilon*delta),
        "stellar-child-bc": (orient(b, c, stellar), (1-2*epsilon)*delta),
        "stellar-child-ca": (orient(c, a, stellar), epsilon*delta),
        "stellar-oriented-area-sum": (
            orient(a, b, stellar)+orient(b, c, stellar)+orient(c, a, stellar), delta),
        "common-witness-convex-variance": (
            (1-u-v)*norm(a-q)+u*norm(b-q)+v*norm(c-q),
            norm(bary-q)+differences),
        "stellar-limit-vanishing-displacement": (
            norm(stellar-a), epsilon**2*norm(b+c-2*a)),
    }
    return variables, identities


def canonical():
    variables, identities = expressions()
    return {
        "schema": SCHEMA, "variables": list(VARIABLES),
        "explicit_ordered_real_hypotheses": list(HYPOTHESES),
        "continuous_and_topological_scope": list(SCOPE),
        "identities": {name: {"left": sparse.encode(left, variables), "right": sparse.encode(right, variables)}
                       for name, (left, right) in identities.items()},
    }


def gate(certificate):
    if (not isinstance(certificate, dict) or set(certificate) != {
            "schema", "variables", "explicit_ordered_real_hypotheses",
            "continuous_and_topological_scope", "identities"}
            or certificate["schema"] != SCHEMA or certificate["variables"] != list(VARIABLES)
            or certificate["explicit_ordered_real_hypotheses"] != list(HYPOTHESES)
            or certificate["continuous_and_topological_scope"] != list(SCOPE)):
        raise ValueError("embedded/starred bridge omitted a premise or promoted its scope")
    variables, identities = expressions()
    if set(certificate["identities"]) != set(identities):
        raise ValueError("embedded/starred bridge omitted a universal identity")
    for name, (left, right) in identities.items():
        item = certificate["identities"][name]
        if set(item) != {"left", "right"}:
            raise ValueError("unknown universal bridge identity fields")
        actual_left, actual_right = (sparse.decode(item[side], variables) for side in ("left", "right"))
        if (sp.expand(actual_left-left) != 0 or sp.expand(actual_right-right) != 0
                or sp.expand(actual_left-actual_right) != 0):
            raise ValueError("universal empty-circle or stellar identity failed")
    return {
        "universal_exact_empty_circle_stellar_identities_checked": len(identities),
        "polynomial_checks_symbolic_NOT_finite_point_sampling": True,
        "written_continuous_disk_dual_and_rotation_argument_still_separate_from_code": True,
        "corner_copy_shadow_and_embedded_limit_scope_explicit": True,
        "original_owner_labels_and_zero_shadow_cell_areas_preserved": True,
        "all_existing_area_formulas_and_source_interfaces_NOT_reproved_by_this_gate": True,
        "formal_machine_geometric_reduction_proved": False,
        "new_geometric_payments": 0, "global_lower_bound_proved": False,
        "global_optimality_proved": False,
    }
